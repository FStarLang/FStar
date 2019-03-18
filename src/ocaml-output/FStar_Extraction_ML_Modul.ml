open Prims
type env_t = FStar_Extraction_ML_UEnv.uenv
let (fail_exp :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun lid  ->
    fun t  ->
      let uu____63766 =
        let uu____63773 =
          let uu____63774 =
            let uu____63791 =
              FStar_Syntax_Syntax.fvar FStar_Parser_Const.failwith_lid
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            let uu____63794 =
              let uu____63805 = FStar_Syntax_Syntax.iarg t  in
              let uu____63814 =
                let uu____63825 =
                  let uu____63834 =
                    let uu____63835 =
                      let uu____63842 =
                        let uu____63843 =
                          let uu____63844 =
                            let uu____63850 =
                              let uu____63852 =
                                FStar_Syntax_Print.lid_to_string lid  in
                              Prims.op_Hat "Not yet implemented:" uu____63852
                               in
                            (uu____63850, FStar_Range.dummyRange)  in
                          FStar_Const.Const_string uu____63844  in
                        FStar_Syntax_Syntax.Tm_constant uu____63843  in
                      FStar_Syntax_Syntax.mk uu____63842  in
                    uu____63835 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange
                     in
                  FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____63834
                   in
                [uu____63825]  in
              uu____63805 :: uu____63814  in
            (uu____63791, uu____63794)  in
          FStar_Syntax_Syntax.Tm_app uu____63774  in
        FStar_Syntax_Syntax.mk uu____63773  in
      uu____63766 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (always_fail :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.letbinding)
  =
  fun lid  ->
    fun t  ->
      let imp =
        let uu____63918 = FStar_Syntax_Util.arrow_formals t  in
        match uu____63918 with
        | ([],t1) ->
            let b =
              let uu____63961 =
                FStar_Syntax_Syntax.gen_bv "_" FStar_Pervasives_Native.None
                  t1
                 in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____63961
               in
            let uu____63969 = fail_exp lid t1  in
            FStar_Syntax_Util.abs [b] uu____63969
              FStar_Pervasives_Native.None
        | (bs,t1) ->
            let uu____64006 = fail_exp lid t1  in
            FStar_Syntax_Util.abs bs uu____64006 FStar_Pervasives_Native.None
         in
      let lb =
        let uu____64010 =
          let uu____64015 =
            FStar_Syntax_Syntax.lid_as_fv lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Util.Inr uu____64015  in
        {
          FStar_Syntax_Syntax.lbname = uu____64010;
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
  'Auu____64037 . 'Auu____64037 Prims.list -> ('Auu____64037 * 'Auu____64037)
  =
  fun uu___612_64048  ->
    match uu___612_64048 with
    | a::b::[] -> (a, b)
    | uu____64053 -> failwith "Expected a list with 2 elements"
  
let (flag_of_qual :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option)
  =
  fun uu___613_64068  ->
    match uu___613_64068 with
    | FStar_Syntax_Syntax.Assumption  ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Assumed
    | FStar_Syntax_Syntax.Private  ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Private
    | FStar_Syntax_Syntax.NoExtract  ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.NoExtract
    | uu____64071 -> FStar_Pervasives_Native.None
  
let rec (extract_meta :
  FStar_Syntax_Syntax.term ->
    FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option)
  =
  fun x  ->
    let uu____64080 = FStar_Syntax_Subst.compress x  in
    match uu____64080 with
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
        FStar_Syntax_Syntax.pos = uu____64084;
        FStar_Syntax_Syntax.vars = uu____64085;_} ->
        let uu____64088 =
          let uu____64090 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____64090  in
        (match uu____64088 with
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
         | uu____64100 -> FStar_Pervasives_Native.None)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____64103;
             FStar_Syntax_Syntax.vars = uu____64104;_},({
                                                          FStar_Syntax_Syntax.n
                                                            =
                                                            FStar_Syntax_Syntax.Tm_constant
                                                            (FStar_Const.Const_string
                                                            (s,uu____64106));
                                                          FStar_Syntax_Syntax.pos
                                                            = uu____64107;
                                                          FStar_Syntax_Syntax.vars
                                                            = uu____64108;_},uu____64109)::[]);
        FStar_Syntax_Syntax.pos = uu____64110;
        FStar_Syntax_Syntax.vars = uu____64111;_} ->
        let uu____64154 =
          let uu____64156 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____64156  in
        (match uu____64154 with
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
         | uu____64165 -> FStar_Pervasives_Native.None)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("KremlinPrivate",uu____64167));
        FStar_Syntax_Syntax.pos = uu____64168;
        FStar_Syntax_Syntax.vars = uu____64169;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Private
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("c_inline",uu____64174));
        FStar_Syntax_Syntax.pos = uu____64175;
        FStar_Syntax_Syntax.vars = uu____64176;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.CInline
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("substitute",uu____64181));
        FStar_Syntax_Syntax.pos = uu____64182;
        FStar_Syntax_Syntax.vars = uu____64183;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Substitute
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_meta (x1,uu____64189);
        FStar_Syntax_Syntax.pos = uu____64190;
        FStar_Syntax_Syntax.vars = uu____64191;_} -> extract_meta x1
    | uu____64198 -> FStar_Pervasives_Native.None
  
let (extract_metadata :
  FStar_Syntax_Syntax.term Prims.list ->
    FStar_Extraction_ML_Syntax.meta Prims.list)
  = fun metas  -> FStar_List.choose extract_meta metas 
let binders_as_mlty_binders :
  'Auu____64218 .
    FStar_Extraction_ML_UEnv.uenv ->
      (FStar_Syntax_Syntax.bv * 'Auu____64218) Prims.list ->
        (FStar_Extraction_ML_UEnv.uenv * Prims.string Prims.list)
  =
  fun env  ->
    fun bs  ->
      FStar_Util.fold_map
        (fun env1  ->
           fun uu____64260  ->
             match uu____64260 with
             | (bv,uu____64271) ->
                 let uu____64272 =
                   let uu____64273 =
                     let uu____64276 =
                       let uu____64277 =
                         FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv  in
                       FStar_Extraction_ML_Syntax.MLTY_Var uu____64277  in
                     FStar_Pervasives_Native.Some uu____64276  in
                   FStar_Extraction_ML_UEnv.extend_ty env1 bv uu____64273  in
                 let uu____64279 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv
                    in
                 (uu____64272, uu____64279)) env bs
  
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
    let uu____64480 = FStar_Syntax_Print.lid_to_string i.iname  in
    let uu____64482 = FStar_Syntax_Print.binders_to_string " " i.iparams  in
    let uu____64485 = FStar_Syntax_Print.term_to_string i.ityp  in
    let uu____64487 =
      let uu____64489 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d  ->
                let uu____64503 = FStar_Syntax_Print.lid_to_string d.dname
                   in
                let uu____64505 =
                  let uu____64507 = FStar_Syntax_Print.term_to_string d.dtyp
                     in
                  Prims.op_Hat " : " uu____64507  in
                Prims.op_Hat uu____64503 uu____64505))
         in
      FStar_All.pipe_right uu____64489 (FStar_String.concat "\n\t\t")  in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____64480 uu____64482
      uu____64485 uu____64487
  
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
          let uu____64561 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun se  ->
                   match se.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,_us,bs,t,_mut_i,datas) ->
                       let uu____64609 = FStar_Syntax_Subst.open_term bs t
                          in
                       (match uu____64609 with
                        | (bs1,t1) ->
                            let datas1 =
                              FStar_All.pipe_right ses
                                (FStar_List.collect
                                   (fun se1  ->
                                      match se1.FStar_Syntax_Syntax.sigel
                                      with
                                      | FStar_Syntax_Syntax.Sig_datacon
                                          (d,uu____64648,t2,l',nparams,uu____64652)
                                          when FStar_Ident.lid_equals l l' ->
                                          let uu____64659 =
                                            FStar_Syntax_Util.arrow_formals
                                              t2
                                             in
                                          (match uu____64659 with
                                           | (bs',body) ->
                                               let uu____64698 =
                                                 FStar_Util.first_N
                                                   (FStar_List.length bs1)
                                                   bs'
                                                  in
                                               (match uu____64698 with
                                                | (bs_params,rest) ->
                                                    let subst1 =
                                                      FStar_List.map2
                                                        (fun uu____64789  ->
                                                           fun uu____64790 
                                                             ->
                                                             match (uu____64789,
                                                                    uu____64790)
                                                             with
                                                             | ((b',uu____64816),
                                                                (b,uu____64818))
                                                                 ->
                                                                 let uu____64839
                                                                   =
                                                                   let uu____64846
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    b  in
                                                                   (b',
                                                                    uu____64846)
                                                                    in
                                                                 FStar_Syntax_Syntax.NT
                                                                   uu____64839)
                                                        bs_params bs1
                                                       in
                                                    let t3 =
                                                      let uu____64852 =
                                                        let uu____64853 =
                                                          FStar_Syntax_Syntax.mk_Total
                                                            body
                                                           in
                                                        FStar_Syntax_Util.arrow
                                                          rest uu____64853
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____64852
                                                        (FStar_Syntax_Subst.subst
                                                           subst1)
                                                       in
                                                    [{ dname = d; dtyp = t3 }]))
                                      | uu____64856 -> []))
                               in
                            let metadata =
                              let uu____64860 =
                                extract_metadata
                                  (FStar_List.append
                                     se.FStar_Syntax_Syntax.sigattrs attrs)
                                 in
                              let uu____64863 =
                                FStar_List.choose flag_of_qual quals  in
                              FStar_List.append uu____64860 uu____64863  in
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
                   | uu____64870 -> (env1, [])) env ses
             in
          match uu____64561 with
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
    let uu___820_65050 = empty_iface  in
    {
      iface_module_name = (uu___820_65050.iface_module_name);
      iface_bindings = fvs;
      iface_tydefs = (uu___820_65050.iface_tydefs);
      iface_type_names = (uu___820_65050.iface_type_names)
    }
  
let (iface_of_tydefs : FStar_Extraction_ML_UEnv.tydef Prims.list -> iface) =
  fun tds  ->
    let uu___823_65061 = empty_iface  in
    let uu____65062 =
      FStar_List.map (fun td  -> td.FStar_Extraction_ML_UEnv.tydef_fv) tds
       in
    {
      iface_module_name = (uu___823_65061.iface_module_name);
      iface_bindings = (uu___823_65061.iface_bindings);
      iface_tydefs = tds;
      iface_type_names = uu____65062
    }
  
let (iface_of_type_names : FStar_Syntax_Syntax.fv Prims.list -> iface) =
  fun fvs  ->
    let uu___827_65077 = empty_iface  in
    {
      iface_module_name = (uu___827_65077.iface_module_name);
      iface_bindings = (uu___827_65077.iface_bindings);
      iface_tydefs = (uu___827_65077.iface_tydefs);
      iface_type_names = fvs
    }
  
let (iface_union : iface -> iface -> iface) =
  fun if1  ->
    fun if2  ->
      let uu____65089 =
        if if1.iface_module_name <> if1.iface_module_name
        then failwith "Union not defined"
        else if1.iface_module_name  in
      {
        iface_module_name = uu____65089;
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
  'Auu____65134 .
    FStar_Extraction_ML_Syntax.mlpath ->
      ('Auu____65134 * FStar_Extraction_ML_Syntax.mlty) -> Prims.string
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
      let uu____65166 =
        FStar_Extraction_ML_Code.string_of_mlexpr cm
          e.FStar_Extraction_ML_UEnv.exp_b_expr
         in
      let uu____65168 =
        tscheme_to_string cm e.FStar_Extraction_ML_UEnv.exp_b_tscheme  in
      let uu____65170 =
        FStar_Util.string_of_bool e.FStar_Extraction_ML_UEnv.exp_b_inst_ok
         in
      FStar_Util.format4
        "{\n\texp_b_name = %s\n\texp_b_expr = %s\n\texp_b_tscheme = %s\n\texp_b_is_rec = %s }"
        e.FStar_Extraction_ML_UEnv.exp_b_name uu____65166 uu____65168
        uu____65170
  
let (print_binding :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_UEnv.exp_binding) ->
      Prims.string)
  =
  fun cm  ->
    fun uu____65188  ->
      match uu____65188 with
      | (fv,exp_binding) ->
          let uu____65196 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____65198 = print_exp_binding cm exp_binding  in
          FStar_Util.format2 "(%s, %s)" uu____65196 uu____65198
  
let (print_tydef :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_UEnv.tydef -> Prims.string)
  =
  fun cm  ->
    fun tydef  ->
      let uu____65213 =
        FStar_Syntax_Print.fv_to_string
          tydef.FStar_Extraction_ML_UEnv.tydef_fv
         in
      let uu____65215 =
        tscheme_to_string cm tydef.FStar_Extraction_ML_UEnv.tydef_def  in
      FStar_Util.format2 "(%s, %s)" uu____65213 uu____65215
  
let (iface_to_string : iface -> Prims.string) =
  fun iface1  ->
    let cm = iface1.iface_module_name  in
    let print_type_name tn = FStar_Syntax_Print.fv_to_string tn  in
    let uu____65233 =
      let uu____65235 =
        FStar_List.map (print_binding cm) iface1.iface_bindings  in
      FStar_All.pipe_right uu____65235 (FStar_String.concat "\n")  in
    let uu____65249 =
      let uu____65251 = FStar_List.map (print_tydef cm) iface1.iface_tydefs
         in
      FStar_All.pipe_right uu____65251 (FStar_String.concat "\n")  in
    let uu____65261 =
      let uu____65263 =
        FStar_List.map print_type_name iface1.iface_type_names  in
      FStar_All.pipe_right uu____65263 (FStar_String.concat "\n")  in
    FStar_Util.format4
      "Interface %s = {\niface_bindings=\n%s;\n\niface_tydefs=\n%s;\n\niface_type_names=%s;\n}"
      (mlpath_to_string iface1.iface_module_name) uu____65233 uu____65249
      uu____65261
  
let (gamma_to_string : FStar_Extraction_ML_UEnv.uenv -> Prims.string) =
  fun env  ->
    let cm = env.FStar_Extraction_ML_UEnv.currentModule  in
    let gamma =
      FStar_List.collect
        (fun uu___614_65296  ->
           match uu___614_65296 with
           | FStar_Extraction_ML_UEnv.Fv (b,e) -> [(b, e)]
           | uu____65313 -> []) env.FStar_Extraction_ML_UEnv.env_bindings
       in
    let uu____65318 =
      let uu____65320 = FStar_List.map (print_binding cm) gamma  in
      FStar_All.pipe_right uu____65320 (FStar_String.concat "\n")  in
    FStar_Util.format1 "Gamma = {\n %s }" uu____65318
  
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
          let uu____65380 =
            let uu____65389 =
              FStar_TypeChecker_Env.open_universes_in
                env.FStar_Extraction_ML_UEnv.env_tcenv
                lb.FStar_Syntax_Syntax.lbunivs
                [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp]
               in
            match uu____65389 with
            | (tcenv,uu____65407,def_typ) ->
                let uu____65413 = as_pair def_typ  in (tcenv, uu____65413)
             in
          match uu____65380 with
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
                let uu____65444 =
                  let uu____65445 = FStar_Syntax_Subst.compress lbdef1  in
                  FStar_All.pipe_right uu____65445 FStar_Syntax_Util.unmeta
                   in
                FStar_All.pipe_right uu____65444 FStar_Syntax_Util.un_uinst
                 in
              let def1 =
                match def.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_abs uu____65453 ->
                    FStar_Extraction_ML_Term.normalize_abs def
                | uu____65472 -> def  in
              let uu____65473 =
                match def1.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____65484) ->
                    FStar_Syntax_Subst.open_term bs body
                | uu____65509 -> ([], def1)  in
              (match uu____65473 with
               | (bs,body) ->
                   let assumed =
                     FStar_Util.for_some
                       (fun uu___615_65529  ->
                          match uu___615_65529 with
                          | FStar_Syntax_Syntax.Assumption  -> true
                          | uu____65532 -> false) quals
                      in
                   let uu____65534 = binders_as_mlty_binders env bs  in
                   (match uu____65534 with
                    | (env1,ml_bs) ->
                        let body1 =
                          let uu____65561 =
                            FStar_Extraction_ML_Term.term_as_mlty env1 body
                             in
                          FStar_All.pipe_right uu____65561
                            (FStar_Extraction_ML_Util.eraseTypeDeep
                               (FStar_Extraction_ML_Util.udelta_unfold env1))
                           in
                        let mangled_projector =
                          let uu____65566 =
                            FStar_All.pipe_right quals
                              (FStar_Util.for_some
                                 (fun uu___616_65573  ->
                                    match uu___616_65573 with
                                    | FStar_Syntax_Syntax.Projector
                                        uu____65575 -> true
                                    | uu____65581 -> false))
                             in
                          if uu____65566
                          then
                            let mname = mangle_projector_lid lid  in
                            FStar_Pervasives_Native.Some
                              ((mname.FStar_Ident.ident).FStar_Ident.idText)
                          else FStar_Pervasives_Native.None  in
                        let metadata =
                          let uu____65595 = extract_metadata attrs  in
                          let uu____65598 =
                            FStar_List.choose flag_of_qual quals  in
                          FStar_List.append uu____65595 uu____65598  in
                        let td =
                          let uu____65621 = lident_as_mlsymbol lid  in
                          (assumed, uu____65621, mangled_projector, ml_bs,
                            metadata,
                            (FStar_Pervasives_Native.Some
                               (FStar_Extraction_ML_Syntax.MLTD_Abbrev body1)))
                           in
                        let def2 =
                          let uu____65633 =
                            let uu____65634 =
                              let uu____65635 = FStar_Ident.range_of_lid lid
                                 in
                              FStar_Extraction_ML_Util.mlloc_of_range
                                uu____65635
                               in
                            FStar_Extraction_ML_Syntax.MLM_Loc uu____65634
                             in
                          [uu____65633;
                          FStar_Extraction_ML_Syntax.MLM_Ty [td]]  in
                        let uu____65636 =
                          let uu____65641 =
                            FStar_All.pipe_right quals
                              (FStar_Util.for_some
                                 (fun uu___617_65647  ->
                                    match uu___617_65647 with
                                    | FStar_Syntax_Syntax.Assumption  -> true
                                    | FStar_Syntax_Syntax.New  -> true
                                    | uu____65651 -> false))
                             in
                          if uu____65641
                          then
                            let uu____65658 =
                              FStar_Extraction_ML_UEnv.extend_type_name env
                                fv
                               in
                            (uu____65658, (iface_of_type_names [fv]))
                          else
                            (let uu____65661 =
                               FStar_Extraction_ML_UEnv.extend_tydef env fv
                                 td
                                in
                             match uu____65661 with
                             | (env2,tydef) ->
                                 let uu____65672 = iface_of_tydefs [tydef]
                                    in
                                 (env2, uu____65672))
                           in
                        (match uu____65636 with
                         | (env2,iface1) -> (env2, iface1, def2))))
  
let (extract_bundle_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt -> (env_t * iface))
  =
  fun env  ->
    fun se  ->
      let extract_ctor env_iparams ml_tyvars env1 ctor =
        let mlt =
          let uu____65748 =
            FStar_Extraction_ML_Term.term_as_mlty env_iparams ctor.dtyp  in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env_iparams) uu____65748
           in
        let tys = (ml_tyvars, mlt)  in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp  in
        let uu____65755 =
          FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false  in
        match uu____65755 with | (env2,uu____65774,b) -> (env2, (fvv, b))  in
      let extract_one_family env1 ind =
        let uu____65813 = binders_as_mlty_binders env1 ind.iparams  in
        match uu____65813 with
        | (env_iparams,vars) ->
            let uu____65841 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor env_iparams vars) env1)
               in
            (match uu____65841 with | (env2,ctors) -> (env2, ctors))
         in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____65905,t,uu____65907,uu____65908,uu____65909);
            FStar_Syntax_Syntax.sigrng = uu____65910;
            FStar_Syntax_Syntax.sigquals = uu____65911;
            FStar_Syntax_Syntax.sigmeta = uu____65912;
            FStar_Syntax_Syntax.sigattrs = uu____65913;_}::[],uu____65914),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____65933 = extract_ctor env [] env { dname = l; dtyp = t }
             in
          (match uu____65933 with
           | (env1,ctor) -> (env1, (iface_of_bindings [ctor])))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____65966),quals) ->
          let uu____65980 =
            bundle_as_inductive_families env ses quals
              se.FStar_Syntax_Syntax.sigattrs
             in
          (match uu____65980 with
           | (env1,ifams) ->
               let uu____65997 =
                 FStar_Util.fold_map extract_one_family env1 ifams  in
               (match uu____65997 with
                | (env2,td) ->
                    let uu____66038 =
                      let uu____66039 =
                        let uu____66040 =
                          FStar_List.map (fun x  -> x.ifv) ifams  in
                        iface_of_type_names uu____66040  in
                      iface_union uu____66039
                        (iface_of_bindings (FStar_List.flatten td))
                       in
                    (env2, uu____66038)))
      | uu____66049 -> failwith "Unexpected signature element"
  
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
              let uu____66124 =
                let uu____66126 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun uu___618_66132  ->
                          match uu___618_66132 with
                          | FStar_Syntax_Syntax.Assumption  -> true
                          | uu____66135 -> false))
                   in
                Prims.op_Negation uu____66126  in
              if uu____66124
              then (g, empty_iface, [])
              else
                (let uu____66150 = FStar_Syntax_Util.arrow_formals t  in
                 match uu____66150 with
                 | (bs,uu____66174) ->
                     let fv =
                       FStar_Syntax_Syntax.lid_as_fv lid
                         FStar_Syntax_Syntax.delta_constant
                         FStar_Pervasives_Native.None
                        in
                     let lb =
                       let uu____66197 =
                         FStar_Syntax_Util.abs bs FStar_Syntax_Syntax.t_unit
                           FStar_Pervasives_Native.None
                          in
                       {
                         FStar_Syntax_Syntax.lbname = (FStar_Util.Inr fv);
                         FStar_Syntax_Syntax.lbunivs = univs1;
                         FStar_Syntax_Syntax.lbtyp = t;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_Tot_lid;
                         FStar_Syntax_Syntax.lbdef = uu____66197;
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
        let uu____66260 =
          FStar_Extraction_ML_UEnv.extend_fv' g1 fv ml_name tysc false false
           in
        match uu____66260 with
        | (g2,mangled_name,exp_binding) ->
            ((let uu____66282 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g2.FStar_Extraction_ML_UEnv.env_tcenv)
                  (FStar_Options.Other "ExtractionReify")
                 in
              if uu____66282
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
        (let uu____66318 =
           FStar_All.pipe_left
             (FStar_TypeChecker_Env.debug
                g.FStar_Extraction_ML_UEnv.env_tcenv)
             (FStar_Options.Other "ExtractionReify")
            in
         if uu____66318
         then
           let uu____66323 = FStar_Syntax_Print.term_to_string tm  in
           FStar_Util.print1 "extract_fv term: %s\n" uu____66323
         else ());
        (let uu____66328 =
           let uu____66329 = FStar_Syntax_Subst.compress tm  in
           uu____66329.FStar_Syntax_Syntax.n  in
         match uu____66328 with
         | FStar_Syntax_Syntax.Tm_uinst (tm1,uu____66337) -> extract_fv tm1
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             let mlp =
               FStar_Extraction_ML_Syntax.mlpath_of_lident
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             let uu____66344 = FStar_Extraction_ML_UEnv.lookup_fv g fv  in
             (match uu____66344 with
              | { FStar_Extraction_ML_UEnv.exp_b_name = uu____66349;
                  FStar_Extraction_ML_UEnv.exp_b_expr = uu____66350;
                  FStar_Extraction_ML_UEnv.exp_b_tscheme = tysc;
                  FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____66352;_} ->
                  let uu____66355 =
                    FStar_All.pipe_left
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.MLTY_Top)
                      (FStar_Extraction_ML_Syntax.MLE_Name mlp)
                     in
                  (uu____66355, tysc))
         | uu____66356 ->
             let uu____66357 =
               let uu____66359 =
                 FStar_Range.string_of_range tm.FStar_Syntax_Syntax.pos  in
               let uu____66361 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.format2 "(%s) Not an fv: %s" uu____66359
                 uu____66361
                in
             failwith uu____66357)
         in
      let extract_action g1 a =
        (let uu____66389 =
           FStar_All.pipe_left
             (FStar_TypeChecker_Env.debug
                g1.FStar_Extraction_ML_UEnv.env_tcenv)
             (FStar_Options.Other "ExtractionReify")
            in
         if uu____66389
         then
           let uu____66394 =
             FStar_Syntax_Print.term_to_string
               a.FStar_Syntax_Syntax.action_typ
              in
           let uu____66396 =
             FStar_Syntax_Print.term_to_string
               a.FStar_Syntax_Syntax.action_defn
              in
           FStar_Util.print2 "Action type %s and term %s\n" uu____66394
             uu____66396
         else ());
        (let uu____66401 = FStar_Extraction_ML_UEnv.action_name ed a  in
         match uu____66401 with
         | (a_nm,a_lid) ->
             let lbname =
               let uu____66421 =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some
                      ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                   FStar_Syntax_Syntax.tun
                  in
               FStar_Util.Inl uu____66421  in
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
             let uu____66451 =
               FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb  in
             (match uu____66451 with
              | (a_let,uu____66467,ty) ->
                  ((let uu____66470 =
                      FStar_All.pipe_left
                        (FStar_TypeChecker_Env.debug
                           g1.FStar_Extraction_ML_UEnv.env_tcenv)
                        (FStar_Options.Other "ExtractionReify")
                       in
                    if uu____66470
                    then
                      let uu____66475 =
                        FStar_Extraction_ML_Code.string_of_mlexpr a_nm a_let
                         in
                      FStar_Util.print1 "Extracted action term: %s\n"
                        uu____66475
                    else ());
                   (let uu____66480 =
                      match a_let.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Let
                          ((uu____66503,mllb::[]),uu____66505) ->
                          (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc
                           with
                           | FStar_Pervasives_Native.Some tysc ->
                               ((mllb.FStar_Extraction_ML_Syntax.mllb_def),
                                 tysc)
                           | FStar_Pervasives_Native.None  ->
                               failwith "No type scheme")
                      | uu____66545 -> failwith "Impossible"  in
                    match uu____66480 with
                    | (exp,tysc) ->
                        ((let uu____66583 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug
                                 g1.FStar_Extraction_ML_UEnv.env_tcenv)
                              (FStar_Options.Other "ExtractionReify")
                             in
                          if uu____66583
                          then
                            ((let uu____66589 =
                                FStar_Extraction_ML_Code.string_of_mlty a_nm
                                  (FStar_Pervasives_Native.snd tysc)
                                 in
                              FStar_Util.print1 "Extracted action type: %s\n"
                                uu____66589);
                             FStar_List.iter
                               (fun x  ->
                                  FStar_Util.print1 "and binders: %s\n" x)
                               (FStar_Pervasives_Native.fst tysc))
                          else ());
                         (let uu____66605 = extend_env g1 a_lid a_nm exp tysc
                             in
                          match uu____66605 with
                          | (env,iface1,impl) -> (env, (iface1, impl))))))))
         in
      let uu____66627 =
        let uu____66634 =
          extract_fv
            (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.return_repr)
           in
        match uu____66634 with
        | (return_tm,ty_sc) ->
            let uu____66651 =
              FStar_Extraction_ML_UEnv.monad_op_name ed "return"  in
            (match uu____66651 with
             | (return_nm,return_lid) ->
                 extend_env g return_lid return_nm return_tm ty_sc)
         in
      match uu____66627 with
      | (g1,return_iface,return_decl) ->
          let uu____66676 =
            let uu____66683 =
              extract_fv
                (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.bind_repr)
               in
            match uu____66683 with
            | (bind_tm,ty_sc) ->
                let uu____66700 =
                  FStar_Extraction_ML_UEnv.monad_op_name ed "bind"  in
                (match uu____66700 with
                 | (bind_nm,bind_lid) ->
                     extend_env g1 bind_lid bind_nm bind_tm ty_sc)
             in
          (match uu____66676 with
           | (g2,bind_iface,bind_decl) ->
               let uu____66725 =
                 FStar_Util.fold_map extract_action g2
                   ed.FStar_Syntax_Syntax.actions
                  in
               (match uu____66725 with
                | (g3,actions) ->
                    let uu____66762 = FStar_List.unzip actions  in
                    (match uu____66762 with
                     | (actions_iface,actions1) ->
                         let uu____66789 =
                           iface_union_l (return_iface :: bind_iface ::
                             actions_iface)
                            in
                         (g3, uu____66789, (return_decl :: bind_decl ::
                           actions1)))))
  
let (extract_sigelt_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle uu____66811 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____66820 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_datacon uu____66837 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) when
          FStar_Extraction_ML_Term.is_arity g t ->
          let uu____66856 =
            extract_type_declaration g lid se.FStar_Syntax_Syntax.sigquals
              se.FStar_Syntax_Syntax.sigattrs univs1 t
             in
          (match uu____66856 with | (env,iface1,uu____66871) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____66877) when
          FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp ->
          let uu____66886 =
            extract_typ_abbrev g se.FStar_Syntax_Syntax.sigquals
              se.FStar_Syntax_Syntax.sigattrs lb
             in
          (match uu____66886 with | (env,iface1,uu____66901) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,_univs,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let uu____66912 =
            (FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption))
              &&
              (let uu____66918 =
                 FStar_TypeChecker_Util.must_erase_for_extraction
                   g.FStar_Extraction_ML_UEnv.env_tcenv t
                  in
               Prims.op_Negation uu____66918)
             in
          if uu____66912
          then
            let uu____66925 =
              let uu____66936 =
                let uu____66937 =
                  let uu____66940 = always_fail lid t  in [uu____66940]  in
                (false, uu____66937)  in
              FStar_Extraction_ML_Term.extract_lb_iface g uu____66936  in
            (match uu____66925 with
             | (g1,bindings) -> (g1, (iface_of_bindings bindings)))
          else (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____66966) ->
          let uu____66971 = FStar_Extraction_ML_Term.extract_lb_iface g lbs
             in
          (match uu____66971 with
           | (g1,bindings) -> (g1, (iface_of_bindings bindings)))
      | FStar_Syntax_Syntax.Sig_main uu____67000 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____67001 ->
          (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_assume uu____67002 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____67009 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____67010 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          (FStar_Syntax_Util.process_pragma p se.FStar_Syntax_Syntax.sigrng;
           (g, empty_iface))
      | FStar_Syntax_Syntax.Sig_splice uu____67025 ->
          failwith "impossible: trying to extract splice"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____67038 =
            (FStar_TypeChecker_Env.is_reifiable_effect
               g.FStar_Extraction_ML_UEnv.env_tcenv
               ed.FStar_Syntax_Syntax.mname)
              && (FStar_List.isEmpty ed.FStar_Syntax_Syntax.binders)
             in
          if uu____67038
          then
            let uu____67051 = extract_reifiable_effect g ed  in
            (match uu____67051 with
             | (env,iface1,uu____67066) -> (env, iface1))
          else (g, empty_iface)
  
let (extract_iface' :
  env_t ->
    FStar_Syntax_Syntax.modul -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun modul  ->
      let uu____67088 = FStar_Options.interactive ()  in
      if uu____67088
      then (g, empty_iface)
      else
        (let uu____67097 = FStar_Options.restore_cmd_line_options true  in
         let decls = modul.FStar_Syntax_Syntax.declarations  in
         let iface1 =
           let uu___1166_67101 = empty_iface  in
           {
             iface_module_name = (g.FStar_Extraction_ML_UEnv.currentModule);
             iface_bindings = (uu___1166_67101.iface_bindings);
             iface_tydefs = (uu___1166_67101.iface_tydefs);
             iface_type_names = (uu___1166_67101.iface_type_names)
           }  in
         let res =
           FStar_List.fold_left
             (fun uu____67119  ->
                fun se  ->
                  match uu____67119 with
                  | (g1,iface2) ->
                      let uu____67131 = extract_sigelt_iface g1 se  in
                      (match uu____67131 with
                       | (g2,iface') ->
                           let uu____67142 = iface_union iface2 iface'  in
                           (g2, uu____67142))) (g, iface1) decls
            in
         (let uu____67144 = FStar_Options.restore_cmd_line_options true  in
          FStar_All.pipe_left (fun a1  -> ()) uu____67144);
         res)
  
let (extract_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.modul -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun modul  ->
      let uu____67161 = FStar_Options.debug_any ()  in
      if uu____67161
      then
        let uu____67168 =
          FStar_Util.format1 "Extracted interface of %s"
            (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
           in
        FStar_Util.measure_execution_time uu____67168
          (fun uu____67176  -> extract_iface' g modul)
      else extract_iface' g modul
  
let (extend_with_iface :
  FStar_Extraction_ML_UEnv.uenv -> iface -> FStar_Extraction_ML_UEnv.uenv) =
  fun g  ->
    fun iface1  ->
      let uu___1184_67190 = g  in
      let uu____67191 =
        let uu____67194 =
          FStar_List.map (fun _67201  -> FStar_Extraction_ML_UEnv.Fv _67201)
            iface1.iface_bindings
           in
        FStar_List.append uu____67194 g.FStar_Extraction_ML_UEnv.env_bindings
         in
      {
        FStar_Extraction_ML_UEnv.env_tcenv =
          (uu___1184_67190.FStar_Extraction_ML_UEnv.env_tcenv);
        FStar_Extraction_ML_UEnv.env_bindings = uu____67191;
        FStar_Extraction_ML_UEnv.tydefs =
          (FStar_List.append iface1.iface_tydefs
             g.FStar_Extraction_ML_UEnv.tydefs);
        FStar_Extraction_ML_UEnv.type_names =
          (FStar_List.append iface1.iface_type_names
             g.FStar_Extraction_ML_UEnv.type_names);
        FStar_Extraction_ML_UEnv.currentModule =
          (uu___1184_67190.FStar_Extraction_ML_UEnv.currentModule)
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
          let uu____67279 =
            FStar_Extraction_ML_Term.term_as_mlty env_iparams ctor.dtyp  in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env_iparams) uu____67279
           in
        let steps =
          [FStar_TypeChecker_Env.Inlining;
          FStar_TypeChecker_Env.UnfoldUntil
            FStar_Syntax_Syntax.delta_constant;
          FStar_TypeChecker_Env.EraseUniverses;
          FStar_TypeChecker_Env.AllowUnboundUniverses]  in
        let names1 =
          let uu____67287 =
            let uu____67288 =
              let uu____67291 =
                FStar_TypeChecker_Normalize.normalize steps
                  env_iparams.FStar_Extraction_ML_UEnv.env_tcenv ctor.dtyp
                 in
              FStar_Syntax_Subst.compress uu____67291  in
            uu____67288.FStar_Syntax_Syntax.n  in
          match uu____67287 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,uu____67296) ->
              FStar_List.map
                (fun uu____67329  ->
                   match uu____67329 with
                   | ({ FStar_Syntax_Syntax.ppname = ppname;
                        FStar_Syntax_Syntax.index = uu____67338;
                        FStar_Syntax_Syntax.sort = uu____67339;_},uu____67340)
                       -> ppname.FStar_Ident.idText) bs
          | uu____67348 -> []  in
        let tys = (ml_tyvars, mlt)  in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp  in
        let uu____67356 =
          FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false  in
        match uu____67356 with
        | (env2,uu____67383,uu____67384) ->
            let uu____67387 =
              let uu____67400 = lident_as_mlsymbol ctor.dname  in
              let uu____67402 =
                let uu____67410 = FStar_Extraction_ML_Util.argTypes mlt  in
                FStar_List.zip names1 uu____67410  in
              (uu____67400, uu____67402)  in
            (env2, uu____67387)
         in
      let extract_one_family env1 ind =
        let uu____67471 = binders_as_mlty_binders env1 ind.iparams  in
        match uu____67471 with
        | (env_iparams,vars) ->
            let uu____67515 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor env_iparams vars) env1)
               in
            (match uu____67515 with
             | (env2,ctors) ->
                 let uu____67622 = FStar_Syntax_Util.arrow_formals ind.ityp
                    in
                 (match uu____67622 with
                  | (indices,uu____67664) ->
                      let ml_params =
                        let uu____67689 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____67715  ->
                                    let uu____67723 =
                                      FStar_Util.string_of_int i  in
                                    Prims.op_Hat "'dummyV" uu____67723))
                           in
                        FStar_List.append vars uu____67689  in
                      let tbody =
                        let uu____67728 =
                          FStar_Util.find_opt
                            (fun uu___619_67733  ->
                               match uu___619_67733 with
                               | FStar_Syntax_Syntax.RecordType uu____67735
                                   -> true
                               | uu____67745 -> false) ind.iquals
                           in
                        match uu____67728 with
                        | FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                            let uu____67757 = FStar_List.hd ctors  in
                            (match uu____67757 with
                             | (uu____67782,c_ty) ->
                                 let fields =
                                   FStar_List.map2
                                     (fun id1  ->
                                        fun uu____67826  ->
                                          match uu____67826 with
                                          | (uu____67837,ty) ->
                                              let lid =
                                                FStar_Ident.lid_of_ids
                                                  (FStar_List.append ns [id1])
                                                 in
                                              let uu____67842 =
                                                lident_as_mlsymbol lid  in
                                              (uu____67842, ty)) ids c_ty
                                    in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____67845 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors
                         in
                      let uu____67848 =
                        let uu____67871 = lident_as_mlsymbol ind.iname  in
                        (false, uu____67871, FStar_Pervasives_Native.None,
                          ml_params, (ind.imetadata),
                          (FStar_Pervasives_Native.Some tbody))
                         in
                      (env2, uu____67848)))
         in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____67916,t,uu____67918,uu____67919,uu____67920);
            FStar_Syntax_Syntax.sigrng = uu____67921;
            FStar_Syntax_Syntax.sigquals = uu____67922;
            FStar_Syntax_Syntax.sigmeta = uu____67923;
            FStar_Syntax_Syntax.sigattrs = uu____67924;_}::[],uu____67925),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____67944 = extract_ctor env [] env { dname = l; dtyp = t }
             in
          (match uu____67944 with
           | (env1,ctor) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____67997),quals) ->
          let uu____68011 =
            bundle_as_inductive_families env ses quals
              se.FStar_Syntax_Syntax.sigattrs
             in
          (match uu____68011 with
           | (env1,ifams) ->
               let uu____68030 =
                 FStar_Util.fold_map extract_one_family env1 ifams  in
               (match uu____68030 with
                | (env2,td) -> (env2, [FStar_Extraction_ML_Syntax.MLM_Ty td])))
      | uu____68139 -> failwith "Unexpected signature element"
  
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
             let uu____68197 = FStar_Syntax_Util.head_and_args t  in
             match uu____68197 with
             | (head1,args) ->
                 let uu____68245 =
                   let uu____68247 =
                     FStar_Syntax_Util.is_fvar FStar_Parser_Const.plugin_attr
                       head1
                      in
                   Prims.op_Negation uu____68247  in
                 if uu____68245
                 then FStar_Pervasives_Native.None
                 else
                   (match args with
                    | ({
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_int (s,uu____68266));
                         FStar_Syntax_Syntax.pos = uu____68267;
                         FStar_Syntax_Syntax.vars = uu____68268;_},uu____68269)::[]
                        ->
                        let uu____68308 =
                          let uu____68312 = FStar_Util.int_of_string s  in
                          FStar_Pervasives_Native.Some uu____68312  in
                        FStar_Pervasives_Native.Some uu____68308
                    | uu____68318 ->
                        FStar_Pervasives_Native.Some
                          FStar_Pervasives_Native.None))
         in
      let uu____68333 =
        let uu____68335 = FStar_Options.codegen ()  in
        uu____68335 <> (FStar_Pervasives_Native.Some FStar_Options.Plugin)
         in
      if uu____68333
      then []
      else
        (let uu____68345 = plugin_with_arity se.FStar_Syntax_Syntax.sigattrs
            in
         match uu____68345 with
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
                      let uu____68387 =
                        let uu____68388 = FStar_Ident.string_of_lid fv_lid1
                           in
                        FStar_Extraction_ML_Syntax.MLC_String uu____68388  in
                      FStar_Extraction_ML_Syntax.MLE_Const uu____68387  in
                    let uu____68390 =
                      FStar_Extraction_ML_Util.interpret_plugin_as_term_fun
                        g.FStar_Extraction_ML_UEnv.env_tcenv fv fv_t
                        arity_opt ml_name_str
                       in
                    match uu____68390 with
                    | FStar_Pervasives_Native.Some
                        (interp,nbe_interp,arity,plugin1) ->
                        let uu____68423 =
                          if plugin1
                          then
                            ("FStar_Tactics_Native.register_plugin",
                              [interp; nbe_interp])
                          else
                            ("FStar_Tactics_Native.register_tactic",
                              [interp])
                           in
                        (match uu____68423 with
                         | (register,args) ->
                             let h =
                               let uu____68460 =
                                 let uu____68461 =
                                   let uu____68462 =
                                     FStar_Ident.lid_of_str register  in
                                   FStar_Extraction_ML_Syntax.mlpath_of_lident
                                     uu____68462
                                    in
                                 FStar_Extraction_ML_Syntax.MLE_Name
                                   uu____68461
                                  in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    FStar_Extraction_ML_Syntax.MLTY_Top)
                                 uu____68460
                                in
                             let arity1 =
                               let uu____68464 =
                                 let uu____68465 =
                                   let uu____68477 =
                                     FStar_Util.string_of_int arity  in
                                   (uu____68477,
                                     FStar_Pervasives_Native.None)
                                    in
                                 FStar_Extraction_ML_Syntax.MLC_Int
                                   uu____68465
                                  in
                               FStar_Extraction_ML_Syntax.MLE_Const
                                 uu____68464
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
              | uu____68506 -> []))
  
let rec (extract_sig :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list))
  =
  fun g  ->
    fun se  ->
      FStar_Extraction_ML_UEnv.debug g
        (fun u  ->
           let uu____68534 = FStar_Syntax_Print.sigelt_to_string se  in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____68534);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle uu____68543 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____68552 ->
           extract_bundle g se
       | FStar_Syntax_Syntax.Sig_datacon uu____68569 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           FStar_TypeChecker_Env.is_reifiable_effect
             g.FStar_Extraction_ML_UEnv.env_tcenv
             ed.FStar_Syntax_Syntax.mname
           ->
           let uu____68586 = extract_reifiable_effect g ed  in
           (match uu____68586 with | (env,_iface,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_splice uu____68610 ->
           failwith "impossible: trying to extract splice"
       | FStar_Syntax_Syntax.Sig_new_effect uu____68624 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let uu____68630 =
             extract_type_declaration g lid se.FStar_Syntax_Syntax.sigquals
               se.FStar_Syntax_Syntax.sigattrs univs1 t
              in
           (match uu____68630 with | (env,uu____68646,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____68655) when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let uu____68664 =
             extract_typ_abbrev g se.FStar_Syntax_Syntax.sigquals
               se.FStar_Syntax_Syntax.sigattrs lb
              in
           (match uu____68664 with | (env,uu____68680,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____68689) ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____68700 =
             let uu____68709 =
               FStar_Syntax_Util.extract_attr'
                 FStar_Parser_Const.postprocess_extr_with attrs
                in
             match uu____68709 with
             | FStar_Pervasives_Native.None  ->
                 (attrs, FStar_Pervasives_Native.None)
             | FStar_Pervasives_Native.Some
                 (ats,(tau,FStar_Pervasives_Native.None )::uu____68738) ->
                 (ats, (FStar_Pervasives_Native.Some tau))
             | FStar_Pervasives_Native.Some (ats,args) ->
                 (FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng
                    (FStar_Errors.Warning_UnrecognizedAttribute,
                      "Ill-formed application of `postprocess_for_extraction_with`");
                  (attrs, FStar_Pervasives_Native.None))
              in
           (match uu____68700 with
            | (attrs1,post_tau) ->
                let postprocess_lb tau lb =
                  let lbdef =
                    FStar_TypeChecker_Env.postprocess
                      g.FStar_Extraction_ML_UEnv.env_tcenv tau
                      lb.FStar_Syntax_Syntax.lbtyp
                      lb.FStar_Syntax_Syntax.lbdef
                     in
                  let uu___1403_68824 = lb  in
                  {
                    FStar_Syntax_Syntax.lbname =
                      (uu___1403_68824.FStar_Syntax_Syntax.lbname);
                    FStar_Syntax_Syntax.lbunivs =
                      (uu___1403_68824.FStar_Syntax_Syntax.lbunivs);
                    FStar_Syntax_Syntax.lbtyp =
                      (uu___1403_68824.FStar_Syntax_Syntax.lbtyp);
                    FStar_Syntax_Syntax.lbeff =
                      (uu___1403_68824.FStar_Syntax_Syntax.lbeff);
                    FStar_Syntax_Syntax.lbdef = lbdef;
                    FStar_Syntax_Syntax.lbattrs =
                      (uu___1403_68824.FStar_Syntax_Syntax.lbattrs);
                    FStar_Syntax_Syntax.lbpos =
                      (uu___1403_68824.FStar_Syntax_Syntax.lbpos)
                  }  in
                let lbs1 =
                  let uu____68833 =
                    match post_tau with
                    | FStar_Pervasives_Native.Some tau ->
                        FStar_List.map (postprocess_lb tau)
                          (FStar_Pervasives_Native.snd lbs)
                    | FStar_Pervasives_Native.None  ->
                        FStar_Pervasives_Native.snd lbs
                     in
                  ((FStar_Pervasives_Native.fst lbs), uu____68833)  in
                let uu____68851 =
                  let uu____68858 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_let
                         (lbs1, FStar_Syntax_Util.exp_false_bool))
                      FStar_Pervasives_Native.None
                      se.FStar_Syntax_Syntax.sigrng
                     in
                  FStar_Extraction_ML_Term.term_as_mlexpr g uu____68858  in
                (match uu____68851 with
                 | (ml_let,uu____68875,uu____68876) ->
                     (match ml_let.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Let
                          ((flavor,bindings),uu____68885) ->
                          let flags = FStar_List.choose flag_of_qual quals
                             in
                          let flags' = extract_metadata attrs1  in
                          let uu____68902 =
                            FStar_List.fold_left2
                              (fun uu____68928  ->
                                 fun ml_lb  ->
                                   fun uu____68930  ->
                                     match (uu____68928, uu____68930) with
                                     | ((env,ml_lbs),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbname;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uu____68952;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = t;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____68954;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = uu____68955;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____68956;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____68957;_})
                                         ->
                                         let uu____68982 =
                                           FStar_All.pipe_right
                                             ml_lb.FStar_Extraction_ML_Syntax.mllb_meta
                                             (FStar_List.contains
                                                FStar_Extraction_ML_Syntax.Erased)
                                            in
                                         if uu____68982
                                         then (env, ml_lbs)
                                         else
                                           (let lb_lid =
                                              let uu____68999 =
                                                let uu____69002 =
                                                  FStar_Util.right lbname  in
                                                uu____69002.FStar_Syntax_Syntax.fv_name
                                                 in
                                              uu____68999.FStar_Syntax_Syntax.v
                                               in
                                            let flags'' =
                                              let uu____69006 =
                                                let uu____69007 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____69007.FStar_Syntax_Syntax.n
                                                 in
                                              match uu____69006 with
                                              | FStar_Syntax_Syntax.Tm_arrow
                                                  (uu____69012,{
                                                                 FStar_Syntax_Syntax.n
                                                                   =
                                                                   FStar_Syntax_Syntax.Comp
                                                                   {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____69013;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    = e;
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    =
                                                                    uu____69015;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____69016;
                                                                    FStar_Syntax_Syntax.flags
                                                                    =
                                                                    uu____69017;_};
                                                                 FStar_Syntax_Syntax.pos
                                                                   =
                                                                   uu____69018;
                                                                 FStar_Syntax_Syntax.vars
                                                                   =
                                                                   uu____69019;_})
                                                  when
                                                  let uu____69054 =
                                                    FStar_Ident.string_of_lid
                                                      e
                                                     in
                                                  uu____69054 =
                                                    "FStar.HyperStack.ST.StackInline"
                                                  ->
                                                  [FStar_Extraction_ML_Syntax.StackInline]
                                              | uu____69058 -> []  in
                                            let meta =
                                              FStar_List.append flags
                                                (FStar_List.append flags'
                                                   flags'')
                                               in
                                            let ml_lb1 =
                                              let uu___1451_69063 = ml_lb  in
                                              {
                                                FStar_Extraction_ML_Syntax.mllb_name
                                                  =
                                                  (uu___1451_69063.FStar_Extraction_ML_Syntax.mllb_name);
                                                FStar_Extraction_ML_Syntax.mllb_tysc
                                                  =
                                                  (uu___1451_69063.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                FStar_Extraction_ML_Syntax.mllb_add_unit
                                                  =
                                                  (uu___1451_69063.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                FStar_Extraction_ML_Syntax.mllb_def
                                                  =
                                                  (uu___1451_69063.FStar_Extraction_ML_Syntax.mllb_def);
                                                FStar_Extraction_ML_Syntax.mllb_meta
                                                  = meta;
                                                FStar_Extraction_ML_Syntax.print_typ
                                                  =
                                                  (uu___1451_69063.FStar_Extraction_ML_Syntax.print_typ)
                                              }  in
                                            let uu____69064 =
                                              let uu____69069 =
                                                FStar_All.pipe_right quals
                                                  (FStar_Util.for_some
                                                     (fun uu___620_69076  ->
                                                        match uu___620_69076
                                                        with
                                                        | FStar_Syntax_Syntax.Projector
                                                            uu____69078 ->
                                                            true
                                                        | uu____69084 ->
                                                            false))
                                                 in
                                              if uu____69069
                                              then
                                                let mname =
                                                  let uu____69100 =
                                                    mangle_projector_lid
                                                      lb_lid
                                                     in
                                                  FStar_All.pipe_right
                                                    uu____69100
                                                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                                                   in
                                                let uu____69109 =
                                                  let uu____69117 =
                                                    FStar_Util.right lbname
                                                     in
                                                  let uu____69118 =
                                                    FStar_Util.must
                                                      ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc
                                                     in
                                                  FStar_Extraction_ML_UEnv.extend_fv'
                                                    env uu____69117 mname
                                                    uu____69118
                                                    ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                                    false
                                                   in
                                                match uu____69109 with
                                                | (env1,uu____69125,uu____69126)
                                                    ->
                                                    (env1,
                                                      (let uu___1464_69130 =
                                                         ml_lb1  in
                                                       {
                                                         FStar_Extraction_ML_Syntax.mllb_name
                                                           =
                                                           (FStar_Pervasives_Native.snd
                                                              mname);
                                                         FStar_Extraction_ML_Syntax.mllb_tysc
                                                           =
                                                           (uu___1464_69130.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                         FStar_Extraction_ML_Syntax.mllb_add_unit
                                                           =
                                                           (uu___1464_69130.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                         FStar_Extraction_ML_Syntax.mllb_def
                                                           =
                                                           (uu___1464_69130.FStar_Extraction_ML_Syntax.mllb_def);
                                                         FStar_Extraction_ML_Syntax.mllb_meta
                                                           =
                                                           (uu___1464_69130.FStar_Extraction_ML_Syntax.mllb_meta);
                                                         FStar_Extraction_ML_Syntax.print_typ
                                                           =
                                                           (uu___1464_69130.FStar_Extraction_ML_Syntax.print_typ)
                                                       }))
                                              else
                                                (let uu____69137 =
                                                   let uu____69145 =
                                                     FStar_Util.must
                                                       ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc
                                                      in
                                                   FStar_Extraction_ML_UEnv.extend_lb
                                                     env lbname t uu____69145
                                                     ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                                     false
                                                    in
                                                 match uu____69137 with
                                                 | (env1,uu____69152,uu____69153)
                                                     -> (env1, ml_lb1))
                                               in
                                            match uu____69064 with
                                            | (g1,ml_lb2) ->
                                                (g1, (ml_lb2 :: ml_lbs))))
                              (g, []) bindings
                              (FStar_Pervasives_Native.snd lbs1)
                             in
                          (match uu____68902 with
                           | (g1,ml_lbs') ->
                               let uu____69183 =
                                 let uu____69186 =
                                   let uu____69189 =
                                     let uu____69190 =
                                       FStar_Extraction_ML_Util.mlloc_of_range
                                         se.FStar_Syntax_Syntax.sigrng
                                        in
                                     FStar_Extraction_ML_Syntax.MLM_Loc
                                       uu____69190
                                      in
                                   [uu____69189;
                                   FStar_Extraction_ML_Syntax.MLM_Let
                                     (flavor, (FStar_List.rev ml_lbs'))]
                                    in
                                 let uu____69193 =
                                   maybe_register_plugin g1 se  in
                                 FStar_List.append uu____69186 uu____69193
                                  in
                               (g1, uu____69183))
                      | uu____69198 ->
                          let uu____69199 =
                            let uu____69201 =
                              FStar_Extraction_ML_Code.string_of_mlexpr
                                g.FStar_Extraction_ML_UEnv.currentModule
                                ml_let
                               in
                            FStar_Util.format1
                              "Impossible: Translated a let to a non-let: %s"
                              uu____69201
                             in
                          failwith uu____69199)))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____69211,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____69216 =
             (FStar_All.pipe_right quals
                (FStar_List.contains FStar_Syntax_Syntax.Assumption))
               &&
               (let uu____69222 =
                  FStar_TypeChecker_Util.must_erase_for_extraction
                    g.FStar_Extraction_ML_UEnv.env_tcenv t
                   in
                Prims.op_Negation uu____69222)
              in
           if uu____69216
           then
             let always_fail1 =
               let uu___1484_69232 = se  in
               let uu____69233 =
                 let uu____69234 =
                   let uu____69241 =
                     let uu____69242 =
                       let uu____69245 = always_fail lid t  in [uu____69245]
                        in
                     (false, uu____69242)  in
                   (uu____69241, [])  in
                 FStar_Syntax_Syntax.Sig_let uu____69234  in
               {
                 FStar_Syntax_Syntax.sigel = uu____69233;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___1484_69232.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___1484_69232.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___1484_69232.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___1484_69232.FStar_Syntax_Syntax.sigattrs)
               }  in
             let uu____69252 = extract_sig g always_fail1  in
             (match uu____69252 with
              | (g1,mlm) ->
                  let uu____69271 =
                    FStar_Util.find_map quals
                      (fun uu___621_69276  ->
                         match uu___621_69276 with
                         | FStar_Syntax_Syntax.Discriminator l ->
                             FStar_Pervasives_Native.Some l
                         | uu____69280 -> FStar_Pervasives_Native.None)
                     in
                  (match uu____69271 with
                   | FStar_Pervasives_Native.Some l ->
                       let uu____69288 =
                         let uu____69291 =
                           let uu____69292 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng
                              in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____69292  in
                         let uu____69293 =
                           let uu____69296 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l
                              in
                           [uu____69296]  in
                         uu____69291 :: uu____69293  in
                       (g1, uu____69288)
                   | uu____69299 ->
                       let uu____69302 =
                         FStar_Util.find_map quals
                           (fun uu___622_69308  ->
                              match uu___622_69308 with
                              | FStar_Syntax_Syntax.Projector (l,uu____69312)
                                  -> FStar_Pervasives_Native.Some l
                              | uu____69313 -> FStar_Pervasives_Native.None)
                          in
                       (match uu____69302 with
                        | FStar_Pervasives_Native.Some uu____69320 ->
                            (g1, [])
                        | uu____69323 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____69333 = FStar_Extraction_ML_Term.term_as_mlexpr g e  in
           (match uu____69333 with
            | (ml_main,uu____69347,uu____69348) ->
                let uu____69349 =
                  let uu____69352 =
                    let uu____69353 =
                      FStar_Extraction_ML_Util.mlloc_of_range
                        se.FStar_Syntax_Syntax.sigrng
                       in
                    FStar_Extraction_ML_Syntax.MLM_Loc uu____69353  in
                  [uu____69352; FStar_Extraction_ML_Syntax.MLM_Top ml_main]
                   in
                (g, uu____69349))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____69356 ->
           failwith "impossible -- removed by tc.fs"
       | FStar_Syntax_Syntax.Sig_assume uu____69364 -> (g, [])
       | FStar_Syntax_Syntax.Sig_sub_effect uu____69373 -> (g, [])
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____69376 -> (g, [])
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
      let uu____69418 = FStar_Options.restore_cmd_line_options true  in
      let name =
        FStar_Extraction_ML_Syntax.mlpath_of_lident
          m.FStar_Syntax_Syntax.name
         in
      let g1 =
        let uu___1527_69422 = g  in
        let uu____69423 =
          FStar_TypeChecker_Env.set_current_module
            g.FStar_Extraction_ML_UEnv.env_tcenv m.FStar_Syntax_Syntax.name
           in
        {
          FStar_Extraction_ML_UEnv.env_tcenv = uu____69423;
          FStar_Extraction_ML_UEnv.env_bindings =
            (uu___1527_69422.FStar_Extraction_ML_UEnv.env_bindings);
          FStar_Extraction_ML_UEnv.tydefs =
            (uu___1527_69422.FStar_Extraction_ML_UEnv.tydefs);
          FStar_Extraction_ML_UEnv.type_names =
            (uu___1527_69422.FStar_Extraction_ML_UEnv.type_names);
          FStar_Extraction_ML_UEnv.currentModule = name
        }  in
      let uu____69424 =
        FStar_Util.fold_map
          (fun g2  ->
             fun se  ->
               let uu____69443 =
                 FStar_Options.debug_module
                   (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                  in
               if uu____69443
               then
                 let nm =
                   let uu____69454 =
                     FStar_All.pipe_right
                       (FStar_Syntax_Util.lids_of_sigelt se)
                       (FStar_List.map FStar_Ident.string_of_lid)
                      in
                   FStar_All.pipe_right uu____69454
                     (FStar_String.concat ", ")
                    in
                 (FStar_Util.print1 "+++About to extract {%s}\n" nm;
                  (let uu____69471 =
                     FStar_Util.format1 "---Extracted {%s}" nm  in
                   FStar_Util.measure_execution_time uu____69471
                     (fun uu____69481  -> extract_sig g2 se)))
               else extract_sig g2 se) g1 m.FStar_Syntax_Syntax.declarations
         in
      match uu____69424 with
      | (g2,sigs) ->
          let mlm = FStar_List.flatten sigs  in
          let is_kremlin =
            let uu____69503 = FStar_Options.codegen ()  in
            uu____69503 =
              (FStar_Pervasives_Native.Some FStar_Options.Kremlin)
             in
          if
            ((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims") &&
              (is_kremlin ||
                 (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface))
          then
            ((let uu____69518 =
                let uu____69520 = FStar_Options.silent ()  in
                Prims.op_Negation uu____69520  in
              if uu____69518
              then
                let uu____69523 =
                  FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
                FStar_Util.print1 "Extracted module %s\n" uu____69523
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
      (let uu____69598 = FStar_Options.restore_cmd_line_options true  in
       FStar_All.pipe_left (fun a2  -> ()) uu____69598);
      (let uu____69601 =
         let uu____69603 =
           FStar_Options.should_extract
             (m.FStar_Syntax_Syntax.name).FStar_Ident.str
            in
         Prims.op_Negation uu____69603  in
       if uu____69601
       then
         let uu____69606 =
           let uu____69608 =
             FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
           FStar_Util.format1
             "Extract called on a module %s that should not be extracted"
             uu____69608
            in
         failwith uu____69606
       else ());
      (let uu____69613 = FStar_Options.interactive ()  in
       if uu____69613
       then (g, FStar_Pervasives_Native.None)
       else
         (let res =
            let uu____69633 = FStar_Options.debug_any ()  in
            if uu____69633
            then
              let msg =
                let uu____69644 =
                  FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name
                   in
                FStar_Util.format1 "Extracting module %s\n" uu____69644  in
              FStar_Util.measure_execution_time msg
                (fun uu____69654  -> extract' g m)
            else extract' g m  in
          (let uu____69658 = FStar_Options.restore_cmd_line_options true  in
           FStar_All.pipe_left (fun a3  -> ()) uu____69658);
          res))
  
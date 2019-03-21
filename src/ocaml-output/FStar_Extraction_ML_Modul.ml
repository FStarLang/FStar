open Prims
type env_t = FStar_Extraction_ML_UEnv.uenv
let (fail_exp :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun lid  ->
    fun t  ->
      let uu____63799 =
        let uu____63806 =
          let uu____63807 =
            let uu____63824 =
              FStar_Syntax_Syntax.fvar FStar_Parser_Const.failwith_lid
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            let uu____63827 =
              let uu____63838 = FStar_Syntax_Syntax.iarg t  in
              let uu____63847 =
                let uu____63858 =
                  let uu____63867 =
                    let uu____63868 =
                      let uu____63875 =
                        let uu____63876 =
                          let uu____63877 =
                            let uu____63883 =
                              let uu____63885 =
                                FStar_Syntax_Print.lid_to_string lid  in
                              Prims.op_Hat "Not yet implemented:" uu____63885
                               in
                            (uu____63883, FStar_Range.dummyRange)  in
                          FStar_Const.Const_string uu____63877  in
                        FStar_Syntax_Syntax.Tm_constant uu____63876  in
                      FStar_Syntax_Syntax.mk uu____63875  in
                    uu____63868 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange
                     in
                  FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____63867
                   in
                [uu____63858]  in
              uu____63838 :: uu____63847  in
            (uu____63824, uu____63827)  in
          FStar_Syntax_Syntax.Tm_app uu____63807  in
        FStar_Syntax_Syntax.mk uu____63806  in
      uu____63799 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (always_fail :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.letbinding)
  =
  fun lid  ->
    fun t  ->
      let imp =
        let uu____63951 = FStar_Syntax_Util.arrow_formals t  in
        match uu____63951 with
        | ([],t1) ->
            let b =
              let uu____63994 =
                FStar_Syntax_Syntax.gen_bv "_" FStar_Pervasives_Native.None
                  t1
                 in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____63994
               in
            let uu____64002 = fail_exp lid t1  in
            FStar_Syntax_Util.abs [b] uu____64002
              FStar_Pervasives_Native.None
        | (bs,t1) ->
            let uu____64039 = fail_exp lid t1  in
            FStar_Syntax_Util.abs bs uu____64039 FStar_Pervasives_Native.None
         in
      let lb =
        let uu____64043 =
          let uu____64048 =
            FStar_Syntax_Syntax.lid_as_fv lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Util.Inr uu____64048  in
        {
          FStar_Syntax_Syntax.lbname = uu____64043;
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
  'Auu____64070 . 'Auu____64070 Prims.list -> ('Auu____64070 * 'Auu____64070)
  =
  fun uu___612_64081  ->
    match uu___612_64081 with
    | a::b::[] -> (a, b)
    | uu____64086 -> failwith "Expected a list with 2 elements"
  
let (flag_of_qual :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option)
  =
  fun uu___613_64101  ->
    match uu___613_64101 with
    | FStar_Syntax_Syntax.Assumption  ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Assumed
    | FStar_Syntax_Syntax.Private  ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Private
    | FStar_Syntax_Syntax.NoExtract  ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.NoExtract
    | uu____64104 -> FStar_Pervasives_Native.None
  
let rec (extract_meta :
  FStar_Syntax_Syntax.term ->
    FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option)
  =
  fun x  ->
    let uu____64113 = FStar_Syntax_Subst.compress x  in
    match uu____64113 with
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
        FStar_Syntax_Syntax.pos = uu____64117;
        FStar_Syntax_Syntax.vars = uu____64118;_} ->
        let uu____64121 =
          let uu____64123 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____64123  in
        (match uu____64121 with
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
         | uu____64133 -> FStar_Pervasives_Native.None)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____64136;
             FStar_Syntax_Syntax.vars = uu____64137;_},({
                                                          FStar_Syntax_Syntax.n
                                                            =
                                                            FStar_Syntax_Syntax.Tm_constant
                                                            (FStar_Const.Const_string
                                                            (s,uu____64139));
                                                          FStar_Syntax_Syntax.pos
                                                            = uu____64140;
                                                          FStar_Syntax_Syntax.vars
                                                            = uu____64141;_},uu____64142)::[]);
        FStar_Syntax_Syntax.pos = uu____64143;
        FStar_Syntax_Syntax.vars = uu____64144;_} ->
        let uu____64187 =
          let uu____64189 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____64189  in
        (match uu____64187 with
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
         | uu____64198 -> FStar_Pervasives_Native.None)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("KremlinPrivate",uu____64200));
        FStar_Syntax_Syntax.pos = uu____64201;
        FStar_Syntax_Syntax.vars = uu____64202;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Private
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("c_inline",uu____64207));
        FStar_Syntax_Syntax.pos = uu____64208;
        FStar_Syntax_Syntax.vars = uu____64209;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.CInline
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("substitute",uu____64214));
        FStar_Syntax_Syntax.pos = uu____64215;
        FStar_Syntax_Syntax.vars = uu____64216;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Substitute
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_meta (x1,uu____64222);
        FStar_Syntax_Syntax.pos = uu____64223;
        FStar_Syntax_Syntax.vars = uu____64224;_} -> extract_meta x1
    | uu____64231 -> FStar_Pervasives_Native.None
  
let (extract_metadata :
  FStar_Syntax_Syntax.term Prims.list ->
    FStar_Extraction_ML_Syntax.meta Prims.list)
  = fun metas  -> FStar_List.choose extract_meta metas 
let binders_as_mlty_binders :
  'Auu____64251 .
    FStar_Extraction_ML_UEnv.uenv ->
      (FStar_Syntax_Syntax.bv * 'Auu____64251) Prims.list ->
        (FStar_Extraction_ML_UEnv.uenv * Prims.string Prims.list)
  =
  fun env  ->
    fun bs  ->
      FStar_Util.fold_map
        (fun env1  ->
           fun uu____64293  ->
             match uu____64293 with
             | (bv,uu____64304) ->
                 let uu____64305 =
                   let uu____64306 =
                     let uu____64309 =
                       let uu____64310 =
                         FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv  in
                       FStar_Extraction_ML_Syntax.MLTY_Var uu____64310  in
                     FStar_Pervasives_Native.Some uu____64309  in
                   FStar_Extraction_ML_UEnv.extend_ty env1 bv uu____64306  in
                 let uu____64312 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv
                    in
                 (uu____64305, uu____64312)) env bs
  
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
    let uu____64513 = FStar_Syntax_Print.lid_to_string i.iname  in
    let uu____64515 = FStar_Syntax_Print.binders_to_string " " i.iparams  in
    let uu____64518 = FStar_Syntax_Print.term_to_string i.ityp  in
    let uu____64520 =
      let uu____64522 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d  ->
                let uu____64536 = FStar_Syntax_Print.lid_to_string d.dname
                   in
                let uu____64538 =
                  let uu____64540 = FStar_Syntax_Print.term_to_string d.dtyp
                     in
                  Prims.op_Hat " : " uu____64540  in
                Prims.op_Hat uu____64536 uu____64538))
         in
      FStar_All.pipe_right uu____64522 (FStar_String.concat "\n\t\t")  in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____64513 uu____64515
      uu____64518 uu____64520
  
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
          let uu____64594 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun se  ->
                   match se.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,_us,bs,t,_mut_i,datas) ->
                       let uu____64642 = FStar_Syntax_Subst.open_term bs t
                          in
                       (match uu____64642 with
                        | (bs1,t1) ->
                            let datas1 =
                              FStar_All.pipe_right ses
                                (FStar_List.collect
                                   (fun se1  ->
                                      match se1.FStar_Syntax_Syntax.sigel
                                      with
                                      | FStar_Syntax_Syntax.Sig_datacon
                                          (d,uu____64681,t2,l',nparams,uu____64685)
                                          when FStar_Ident.lid_equals l l' ->
                                          let uu____64692 =
                                            FStar_Syntax_Util.arrow_formals
                                              t2
                                             in
                                          (match uu____64692 with
                                           | (bs',body) ->
                                               let uu____64731 =
                                                 FStar_Util.first_N
                                                   (FStar_List.length bs1)
                                                   bs'
                                                  in
                                               (match uu____64731 with
                                                | (bs_params,rest) ->
                                                    let subst1 =
                                                      FStar_List.map2
                                                        (fun uu____64822  ->
                                                           fun uu____64823 
                                                             ->
                                                             match (uu____64822,
                                                                    uu____64823)
                                                             with
                                                             | ((b',uu____64849),
                                                                (b,uu____64851))
                                                                 ->
                                                                 let uu____64872
                                                                   =
                                                                   let uu____64879
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    b  in
                                                                   (b',
                                                                    uu____64879)
                                                                    in
                                                                 FStar_Syntax_Syntax.NT
                                                                   uu____64872)
                                                        bs_params bs1
                                                       in
                                                    let t3 =
                                                      let uu____64885 =
                                                        let uu____64886 =
                                                          FStar_Syntax_Syntax.mk_Total
                                                            body
                                                           in
                                                        FStar_Syntax_Util.arrow
                                                          rest uu____64886
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____64885
                                                        (FStar_Syntax_Subst.subst
                                                           subst1)
                                                       in
                                                    [{ dname = d; dtyp = t3 }]))
                                      | uu____64889 -> []))
                               in
                            let metadata =
                              let uu____64893 =
                                extract_metadata
                                  (FStar_List.append
                                     se.FStar_Syntax_Syntax.sigattrs attrs)
                                 in
                              let uu____64896 =
                                FStar_List.choose flag_of_qual quals  in
                              FStar_List.append uu____64893 uu____64896  in
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
                   | uu____64903 -> (env1, [])) env ses
             in
          match uu____64594 with
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
    let uu___820_65083 = empty_iface  in
    {
      iface_module_name = (uu___820_65083.iface_module_name);
      iface_bindings = fvs;
      iface_tydefs = (uu___820_65083.iface_tydefs);
      iface_type_names = (uu___820_65083.iface_type_names)
    }
  
let (iface_of_tydefs : FStar_Extraction_ML_UEnv.tydef Prims.list -> iface) =
  fun tds  ->
    let uu___823_65094 = empty_iface  in
    let uu____65095 =
      FStar_List.map (fun td  -> td.FStar_Extraction_ML_UEnv.tydef_fv) tds
       in
    {
      iface_module_name = (uu___823_65094.iface_module_name);
      iface_bindings = (uu___823_65094.iface_bindings);
      iface_tydefs = tds;
      iface_type_names = uu____65095
    }
  
let (iface_of_type_names : FStar_Syntax_Syntax.fv Prims.list -> iface) =
  fun fvs  ->
    let uu___827_65110 = empty_iface  in
    {
      iface_module_name = (uu___827_65110.iface_module_name);
      iface_bindings = (uu___827_65110.iface_bindings);
      iface_tydefs = (uu___827_65110.iface_tydefs);
      iface_type_names = fvs
    }
  
let (iface_union : iface -> iface -> iface) =
  fun if1  ->
    fun if2  ->
      let uu____65122 =
        if if1.iface_module_name <> if1.iface_module_name
        then failwith "Union not defined"
        else if1.iface_module_name  in
      {
        iface_module_name = uu____65122;
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
  'Auu____65167 .
    FStar_Extraction_ML_Syntax.mlpath ->
      ('Auu____65167 * FStar_Extraction_ML_Syntax.mlty) -> Prims.string
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
      let uu____65199 =
        FStar_Extraction_ML_Code.string_of_mlexpr cm
          e.FStar_Extraction_ML_UEnv.exp_b_expr
         in
      let uu____65201 =
        tscheme_to_string cm e.FStar_Extraction_ML_UEnv.exp_b_tscheme  in
      let uu____65203 =
        FStar_Util.string_of_bool e.FStar_Extraction_ML_UEnv.exp_b_inst_ok
         in
      FStar_Util.format4
        "{\n\texp_b_name = %s\n\texp_b_expr = %s\n\texp_b_tscheme = %s\n\texp_b_is_rec = %s }"
        e.FStar_Extraction_ML_UEnv.exp_b_name uu____65199 uu____65201
        uu____65203
  
let (print_binding :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_UEnv.exp_binding) ->
      Prims.string)
  =
  fun cm  ->
    fun uu____65221  ->
      match uu____65221 with
      | (fv,exp_binding) ->
          let uu____65229 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____65231 = print_exp_binding cm exp_binding  in
          FStar_Util.format2 "(%s, %s)" uu____65229 uu____65231
  
let (print_tydef :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_UEnv.tydef -> Prims.string)
  =
  fun cm  ->
    fun tydef  ->
      let uu____65246 =
        FStar_Syntax_Print.fv_to_string
          tydef.FStar_Extraction_ML_UEnv.tydef_fv
         in
      let uu____65248 =
        tscheme_to_string cm tydef.FStar_Extraction_ML_UEnv.tydef_def  in
      FStar_Util.format2 "(%s, %s)" uu____65246 uu____65248
  
let (iface_to_string : iface -> Prims.string) =
  fun iface1  ->
    let cm = iface1.iface_module_name  in
    let print_type_name tn = FStar_Syntax_Print.fv_to_string tn  in
    let uu____65266 =
      let uu____65268 =
        FStar_List.map (print_binding cm) iface1.iface_bindings  in
      FStar_All.pipe_right uu____65268 (FStar_String.concat "\n")  in
    let uu____65282 =
      let uu____65284 = FStar_List.map (print_tydef cm) iface1.iface_tydefs
         in
      FStar_All.pipe_right uu____65284 (FStar_String.concat "\n")  in
    let uu____65294 =
      let uu____65296 =
        FStar_List.map print_type_name iface1.iface_type_names  in
      FStar_All.pipe_right uu____65296 (FStar_String.concat "\n")  in
    FStar_Util.format4
      "Interface %s = {\niface_bindings=\n%s;\n\niface_tydefs=\n%s;\n\niface_type_names=%s;\n}"
      (mlpath_to_string iface1.iface_module_name) uu____65266 uu____65282
      uu____65294
  
let (gamma_to_string : FStar_Extraction_ML_UEnv.uenv -> Prims.string) =
  fun env  ->
    let cm = env.FStar_Extraction_ML_UEnv.currentModule  in
    let gamma =
      FStar_List.collect
        (fun uu___614_65329  ->
           match uu___614_65329 with
           | FStar_Extraction_ML_UEnv.Fv (b,e) -> [(b, e)]
           | uu____65346 -> []) env.FStar_Extraction_ML_UEnv.env_bindings
       in
    let uu____65351 =
      let uu____65353 = FStar_List.map (print_binding cm) gamma  in
      FStar_All.pipe_right uu____65353 (FStar_String.concat "\n")  in
    FStar_Util.format1 "Gamma = {\n %s }" uu____65351
  
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
          let uu____65413 =
            let uu____65422 =
              FStar_TypeChecker_Env.open_universes_in
                env.FStar_Extraction_ML_UEnv.env_tcenv
                lb.FStar_Syntax_Syntax.lbunivs
                [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp]
               in
            match uu____65422 with
            | (tcenv,uu____65440,def_typ) ->
                let uu____65446 = as_pair def_typ  in (tcenv, uu____65446)
             in
          match uu____65413 with
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
                let uu____65477 =
                  let uu____65478 = FStar_Syntax_Subst.compress lbdef1  in
                  FStar_All.pipe_right uu____65478 FStar_Syntax_Util.unmeta
                   in
                FStar_All.pipe_right uu____65477 FStar_Syntax_Util.un_uinst
                 in
              let def1 =
                match def.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_abs uu____65486 ->
                    FStar_Extraction_ML_Term.normalize_abs def
                | uu____65505 -> def  in
              let uu____65506 =
                match def1.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____65517) ->
                    FStar_Syntax_Subst.open_term bs body
                | uu____65542 -> ([], def1)  in
              (match uu____65506 with
               | (bs,body) ->
                   let assumed =
                     FStar_Util.for_some
                       (fun uu___615_65562  ->
                          match uu___615_65562 with
                          | FStar_Syntax_Syntax.Assumption  -> true
                          | uu____65565 -> false) quals
                      in
                   let uu____65567 = binders_as_mlty_binders env bs  in
                   (match uu____65567 with
                    | (env1,ml_bs) ->
                        let body1 =
                          let uu____65594 =
                            FStar_Extraction_ML_Term.term_as_mlty env1 body
                             in
                          FStar_All.pipe_right uu____65594
                            (FStar_Extraction_ML_Util.eraseTypeDeep
                               (FStar_Extraction_ML_Util.udelta_unfold env1))
                           in
                        let mangled_projector =
                          let uu____65599 =
                            FStar_All.pipe_right quals
                              (FStar_Util.for_some
                                 (fun uu___616_65606  ->
                                    match uu___616_65606 with
                                    | FStar_Syntax_Syntax.Projector
                                        uu____65608 -> true
                                    | uu____65614 -> false))
                             in
                          if uu____65599
                          then
                            let mname = mangle_projector_lid lid  in
                            FStar_Pervasives_Native.Some
                              ((mname.FStar_Ident.ident).FStar_Ident.idText)
                          else FStar_Pervasives_Native.None  in
                        let metadata =
                          let uu____65628 = extract_metadata attrs  in
                          let uu____65631 =
                            FStar_List.choose flag_of_qual quals  in
                          FStar_List.append uu____65628 uu____65631  in
                        let td =
                          let uu____65654 = lident_as_mlsymbol lid  in
                          (assumed, uu____65654, mangled_projector, ml_bs,
                            metadata,
                            (FStar_Pervasives_Native.Some
                               (FStar_Extraction_ML_Syntax.MLTD_Abbrev body1)))
                           in
                        let def2 =
                          let uu____65666 =
                            let uu____65667 =
                              let uu____65668 = FStar_Ident.range_of_lid lid
                                 in
                              FStar_Extraction_ML_Util.mlloc_of_range
                                uu____65668
                               in
                            FStar_Extraction_ML_Syntax.MLM_Loc uu____65667
                             in
                          [uu____65666;
                          FStar_Extraction_ML_Syntax.MLM_Ty [td]]  in
                        let uu____65669 =
                          let uu____65674 =
                            FStar_All.pipe_right quals
                              (FStar_Util.for_some
                                 (fun uu___617_65680  ->
                                    match uu___617_65680 with
                                    | FStar_Syntax_Syntax.Assumption  -> true
                                    | FStar_Syntax_Syntax.New  -> true
                                    | uu____65684 -> false))
                             in
                          if uu____65674
                          then
                            let uu____65691 =
                              FStar_Extraction_ML_UEnv.extend_type_name env
                                fv
                               in
                            (uu____65691, (iface_of_type_names [fv]))
                          else
                            (let uu____65694 =
                               FStar_Extraction_ML_UEnv.extend_tydef env fv
                                 td
                                in
                             match uu____65694 with
                             | (env2,tydef) ->
                                 let uu____65705 = iface_of_tydefs [tydef]
                                    in
                                 (env2, uu____65705))
                           in
                        (match uu____65669 with
                         | (env2,iface1) -> (env2, iface1, def2))))
  
let (extract_bundle_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt -> (env_t * iface))
  =
  fun env  ->
    fun se  ->
      let extract_ctor env_iparams ml_tyvars env1 ctor =
        let mlt =
          let uu____65781 =
            FStar_Extraction_ML_Term.term_as_mlty env_iparams ctor.dtyp  in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env_iparams) uu____65781
           in
        let tys = (ml_tyvars, mlt)  in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp  in
        let uu____65788 =
          FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false  in
        match uu____65788 with | (env2,uu____65807,b) -> (env2, (fvv, b))  in
      let extract_one_family env1 ind =
        let uu____65846 = binders_as_mlty_binders env1 ind.iparams  in
        match uu____65846 with
        | (env_iparams,vars) ->
            let uu____65874 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor env_iparams vars) env1)
               in
            (match uu____65874 with | (env2,ctors) -> (env2, ctors))
         in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____65938,t,uu____65940,uu____65941,uu____65942);
            FStar_Syntax_Syntax.sigrng = uu____65943;
            FStar_Syntax_Syntax.sigquals = uu____65944;
            FStar_Syntax_Syntax.sigmeta = uu____65945;
            FStar_Syntax_Syntax.sigattrs = uu____65946;_}::[],uu____65947),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____65966 = extract_ctor env [] env { dname = l; dtyp = t }
             in
          (match uu____65966 with
           | (env1,ctor) -> (env1, (iface_of_bindings [ctor])))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____65999),quals) ->
          let uu____66013 =
            bundle_as_inductive_families env ses quals
              se.FStar_Syntax_Syntax.sigattrs
             in
          (match uu____66013 with
           | (env1,ifams) ->
               let uu____66030 =
                 FStar_Util.fold_map extract_one_family env1 ifams  in
               (match uu____66030 with
                | (env2,td) ->
                    let uu____66071 =
                      let uu____66072 =
                        let uu____66073 =
                          FStar_List.map (fun x  -> x.ifv) ifams  in
                        iface_of_type_names uu____66073  in
                      iface_union uu____66072
                        (iface_of_bindings (FStar_List.flatten td))
                       in
                    (env2, uu____66071)))
      | uu____66082 -> failwith "Unexpected signature element"
  
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
              let uu____66157 =
                let uu____66159 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun uu___618_66165  ->
                          match uu___618_66165 with
                          | FStar_Syntax_Syntax.Assumption  -> true
                          | uu____66168 -> false))
                   in
                Prims.op_Negation uu____66159  in
              if uu____66157
              then (g, empty_iface, [])
              else
                (let uu____66183 = FStar_Syntax_Util.arrow_formals t  in
                 match uu____66183 with
                 | (bs,uu____66207) ->
                     let fv =
                       FStar_Syntax_Syntax.lid_as_fv lid
                         FStar_Syntax_Syntax.delta_constant
                         FStar_Pervasives_Native.None
                        in
                     let lb =
                       let uu____66230 =
                         FStar_Syntax_Util.abs bs FStar_Syntax_Syntax.t_unit
                           FStar_Pervasives_Native.None
                          in
                       {
                         FStar_Syntax_Syntax.lbname = (FStar_Util.Inr fv);
                         FStar_Syntax_Syntax.lbunivs = univs1;
                         FStar_Syntax_Syntax.lbtyp = t;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_Tot_lid;
                         FStar_Syntax_Syntax.lbdef = uu____66230;
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
        let uu____66293 =
          FStar_Extraction_ML_UEnv.extend_fv' g1 fv ml_name tysc false false
           in
        match uu____66293 with
        | (g2,mangled_name,exp_binding) ->
            ((let uu____66315 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g2.FStar_Extraction_ML_UEnv.env_tcenv)
                  (FStar_Options.Other "ExtractionReify")
                 in
              if uu____66315
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
        (let uu____66351 =
           FStar_All.pipe_left
             (FStar_TypeChecker_Env.debug
                g.FStar_Extraction_ML_UEnv.env_tcenv)
             (FStar_Options.Other "ExtractionReify")
            in
         if uu____66351
         then
           let uu____66356 = FStar_Syntax_Print.term_to_string tm  in
           FStar_Util.print1 "extract_fv term: %s\n" uu____66356
         else ());
        (let uu____66361 =
           let uu____66362 = FStar_Syntax_Subst.compress tm  in
           uu____66362.FStar_Syntax_Syntax.n  in
         match uu____66361 with
         | FStar_Syntax_Syntax.Tm_uinst (tm1,uu____66370) -> extract_fv tm1
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             let mlp =
               FStar_Extraction_ML_Syntax.mlpath_of_lident
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             let uu____66377 = FStar_Extraction_ML_UEnv.lookup_fv g fv  in
             (match uu____66377 with
              | { FStar_Extraction_ML_UEnv.exp_b_name = uu____66382;
                  FStar_Extraction_ML_UEnv.exp_b_expr = uu____66383;
                  FStar_Extraction_ML_UEnv.exp_b_tscheme = tysc;
                  FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____66385;_} ->
                  let uu____66388 =
                    FStar_All.pipe_left
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.MLTY_Top)
                      (FStar_Extraction_ML_Syntax.MLE_Name mlp)
                     in
                  (uu____66388, tysc))
         | uu____66389 ->
             let uu____66390 =
               let uu____66392 =
                 FStar_Range.string_of_range tm.FStar_Syntax_Syntax.pos  in
               let uu____66394 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.format2 "(%s) Not an fv: %s" uu____66392
                 uu____66394
                in
             failwith uu____66390)
         in
      let extract_action g1 a =
        (let uu____66422 =
           FStar_All.pipe_left
             (FStar_TypeChecker_Env.debug
                g1.FStar_Extraction_ML_UEnv.env_tcenv)
             (FStar_Options.Other "ExtractionReify")
            in
         if uu____66422
         then
           let uu____66427 =
             FStar_Syntax_Print.term_to_string
               a.FStar_Syntax_Syntax.action_typ
              in
           let uu____66429 =
             FStar_Syntax_Print.term_to_string
               a.FStar_Syntax_Syntax.action_defn
              in
           FStar_Util.print2 "Action type %s and term %s\n" uu____66427
             uu____66429
         else ());
        (let uu____66434 = FStar_Extraction_ML_UEnv.action_name ed a  in
         match uu____66434 with
         | (a_nm,a_lid) ->
             let lbname =
               let uu____66454 =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some
                      ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                   FStar_Syntax_Syntax.tun
                  in
               FStar_Util.Inl uu____66454  in
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
             let uu____66484 =
               FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb  in
             (match uu____66484 with
              | (a_let,uu____66500,ty) ->
                  ((let uu____66503 =
                      FStar_All.pipe_left
                        (FStar_TypeChecker_Env.debug
                           g1.FStar_Extraction_ML_UEnv.env_tcenv)
                        (FStar_Options.Other "ExtractionReify")
                       in
                    if uu____66503
                    then
                      let uu____66508 =
                        FStar_Extraction_ML_Code.string_of_mlexpr a_nm a_let
                         in
                      FStar_Util.print1 "Extracted action term: %s\n"
                        uu____66508
                    else ());
                   (let uu____66513 =
                      match a_let.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Let
                          ((uu____66536,mllb::[]),uu____66538) ->
                          (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc
                           with
                           | FStar_Pervasives_Native.Some tysc ->
                               ((mllb.FStar_Extraction_ML_Syntax.mllb_def),
                                 tysc)
                           | FStar_Pervasives_Native.None  ->
                               failwith "No type scheme")
                      | uu____66578 -> failwith "Impossible"  in
                    match uu____66513 with
                    | (exp,tysc) ->
                        ((let uu____66616 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug
                                 g1.FStar_Extraction_ML_UEnv.env_tcenv)
                              (FStar_Options.Other "ExtractionReify")
                             in
                          if uu____66616
                          then
                            ((let uu____66622 =
                                FStar_Extraction_ML_Code.string_of_mlty a_nm
                                  (FStar_Pervasives_Native.snd tysc)
                                 in
                              FStar_Util.print1 "Extracted action type: %s\n"
                                uu____66622);
                             FStar_List.iter
                               (fun x  ->
                                  FStar_Util.print1 "and binders: %s\n" x)
                               (FStar_Pervasives_Native.fst tysc))
                          else ());
                         (let uu____66638 = extend_env g1 a_lid a_nm exp tysc
                             in
                          match uu____66638 with
                          | (env,iface1,impl) -> (env, (iface1, impl))))))))
         in
      let uu____66660 =
        let uu____66667 =
          extract_fv
            (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.return_repr)
           in
        match uu____66667 with
        | (return_tm,ty_sc) ->
            let uu____66684 =
              FStar_Extraction_ML_UEnv.monad_op_name ed "return"  in
            (match uu____66684 with
             | (return_nm,return_lid) ->
                 extend_env g return_lid return_nm return_tm ty_sc)
         in
      match uu____66660 with
      | (g1,return_iface,return_decl) ->
          let uu____66709 =
            let uu____66716 =
              extract_fv
                (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.bind_repr)
               in
            match uu____66716 with
            | (bind_tm,ty_sc) ->
                let uu____66733 =
                  FStar_Extraction_ML_UEnv.monad_op_name ed "bind"  in
                (match uu____66733 with
                 | (bind_nm,bind_lid) ->
                     extend_env g1 bind_lid bind_nm bind_tm ty_sc)
             in
          (match uu____66709 with
           | (g2,bind_iface,bind_decl) ->
               let uu____66758 =
                 FStar_Util.fold_map extract_action g2
                   ed.FStar_Syntax_Syntax.actions
                  in
               (match uu____66758 with
                | (g3,actions) ->
                    let uu____66795 = FStar_List.unzip actions  in
                    (match uu____66795 with
                     | (actions_iface,actions1) ->
                         let uu____66822 =
                           iface_union_l (return_iface :: bind_iface ::
                             actions_iface)
                            in
                         (g3, uu____66822, (return_decl :: bind_decl ::
                           actions1)))))
  
let (extract_sigelt_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle uu____66844 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____66853 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_datacon uu____66870 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) when
          FStar_Extraction_ML_Term.is_arity g t ->
          let uu____66889 =
            extract_type_declaration g lid se.FStar_Syntax_Syntax.sigquals
              se.FStar_Syntax_Syntax.sigattrs univs1 t
             in
          (match uu____66889 with | (env,iface1,uu____66904) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____66910) when
          FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp ->
          let uu____66919 =
            extract_typ_abbrev g se.FStar_Syntax_Syntax.sigquals
              se.FStar_Syntax_Syntax.sigattrs lb
             in
          (match uu____66919 with | (env,iface1,uu____66934) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,_univs,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let uu____66945 =
            (FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption))
              &&
              (let uu____66951 =
                 FStar_TypeChecker_Util.must_erase_for_extraction
                   g.FStar_Extraction_ML_UEnv.env_tcenv t
                  in
               Prims.op_Negation uu____66951)
             in
          if uu____66945
          then
            let uu____66958 =
              let uu____66969 =
                let uu____66970 =
                  let uu____66973 = always_fail lid t  in [uu____66973]  in
                (false, uu____66970)  in
              FStar_Extraction_ML_Term.extract_lb_iface g uu____66969  in
            (match uu____66958 with
             | (g1,bindings) -> (g1, (iface_of_bindings bindings)))
          else (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____66999) ->
          let uu____67004 = FStar_Extraction_ML_Term.extract_lb_iface g lbs
             in
          (match uu____67004 with
           | (g1,bindings) -> (g1, (iface_of_bindings bindings)))
      | FStar_Syntax_Syntax.Sig_main uu____67033 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____67034 ->
          (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_assume uu____67035 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____67042 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____67043 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          (FStar_Syntax_Util.process_pragma p se.FStar_Syntax_Syntax.sigrng;
           (g, empty_iface))
      | FStar_Syntax_Syntax.Sig_splice uu____67058 ->
          failwith "impossible: trying to extract splice"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____67071 =
            (FStar_TypeChecker_Env.is_reifiable_effect
               g.FStar_Extraction_ML_UEnv.env_tcenv
               ed.FStar_Syntax_Syntax.mname)
              && (FStar_List.isEmpty ed.FStar_Syntax_Syntax.binders)
             in
          if uu____67071
          then
            let uu____67084 = extract_reifiable_effect g ed  in
            (match uu____67084 with
             | (env,iface1,uu____67099) -> (env, iface1))
          else (g, empty_iface)
  
let (extract_iface' :
  env_t ->
    FStar_Syntax_Syntax.modul -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun modul  ->
      let uu____67121 = FStar_Options.interactive ()  in
      if uu____67121
      then (g, empty_iface)
      else
        (let uu____67130 = FStar_Options.restore_cmd_line_options true  in
         let decls = modul.FStar_Syntax_Syntax.declarations  in
         let iface1 =
           let uu___1166_67134 = empty_iface  in
           {
             iface_module_name = (g.FStar_Extraction_ML_UEnv.currentModule);
             iface_bindings = (uu___1166_67134.iface_bindings);
             iface_tydefs = (uu___1166_67134.iface_tydefs);
             iface_type_names = (uu___1166_67134.iface_type_names)
           }  in
         let res =
           FStar_List.fold_left
             (fun uu____67152  ->
                fun se  ->
                  match uu____67152 with
                  | (g1,iface2) ->
                      let uu____67164 = extract_sigelt_iface g1 se  in
                      (match uu____67164 with
                       | (g2,iface') ->
                           let uu____67175 = iface_union iface2 iface'  in
                           (g2, uu____67175))) (g, iface1) decls
            in
         (let uu____67177 = FStar_Options.restore_cmd_line_options true  in
          FStar_All.pipe_left (fun a1  -> ()) uu____67177);
         res)
  
let (extract_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.modul -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun modul  ->
      let uu____67194 = FStar_Options.debug_any ()  in
      if uu____67194
      then
        let uu____67201 =
          FStar_Util.format1 "Extracted interface of %s"
            (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
           in
        FStar_Util.measure_execution_time uu____67201
          (fun uu____67209  -> extract_iface' g modul)
      else extract_iface' g modul
  
let (extend_with_iface :
  FStar_Extraction_ML_UEnv.uenv -> iface -> FStar_Extraction_ML_UEnv.uenv) =
  fun g  ->
    fun iface1  ->
      let uu___1184_67223 = g  in
      let uu____67224 =
        let uu____67227 =
          FStar_List.map (fun _67234  -> FStar_Extraction_ML_UEnv.Fv _67234)
            iface1.iface_bindings
           in
        FStar_List.append uu____67227 g.FStar_Extraction_ML_UEnv.env_bindings
         in
      {
        FStar_Extraction_ML_UEnv.env_tcenv =
          (uu___1184_67223.FStar_Extraction_ML_UEnv.env_tcenv);
        FStar_Extraction_ML_UEnv.env_bindings = uu____67224;
        FStar_Extraction_ML_UEnv.tydefs =
          (FStar_List.append iface1.iface_tydefs
             g.FStar_Extraction_ML_UEnv.tydefs);
        FStar_Extraction_ML_UEnv.type_names =
          (FStar_List.append iface1.iface_type_names
             g.FStar_Extraction_ML_UEnv.type_names);
        FStar_Extraction_ML_UEnv.currentModule =
          (uu___1184_67223.FStar_Extraction_ML_UEnv.currentModule)
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
          let uu____67312 =
            FStar_Extraction_ML_Term.term_as_mlty env_iparams ctor.dtyp  in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env_iparams) uu____67312
           in
        let steps =
          [FStar_TypeChecker_Env.Inlining;
          FStar_TypeChecker_Env.UnfoldUntil
            FStar_Syntax_Syntax.delta_constant;
          FStar_TypeChecker_Env.EraseUniverses;
          FStar_TypeChecker_Env.AllowUnboundUniverses]  in
        let names1 =
          let uu____67320 =
            let uu____67321 =
              let uu____67324 =
                FStar_TypeChecker_Normalize.normalize steps
                  env_iparams.FStar_Extraction_ML_UEnv.env_tcenv ctor.dtyp
                 in
              FStar_Syntax_Subst.compress uu____67324  in
            uu____67321.FStar_Syntax_Syntax.n  in
          match uu____67320 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,uu____67329) ->
              FStar_List.map
                (fun uu____67362  ->
                   match uu____67362 with
                   | ({ FStar_Syntax_Syntax.ppname = ppname;
                        FStar_Syntax_Syntax.index = uu____67371;
                        FStar_Syntax_Syntax.sort = uu____67372;_},uu____67373)
                       -> ppname.FStar_Ident.idText) bs
          | uu____67381 -> []  in
        let tys = (ml_tyvars, mlt)  in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp  in
        let uu____67389 =
          FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false  in
        match uu____67389 with
        | (env2,uu____67416,uu____67417) ->
            let uu____67420 =
              let uu____67433 = lident_as_mlsymbol ctor.dname  in
              let uu____67435 =
                let uu____67443 = FStar_Extraction_ML_Util.argTypes mlt  in
                FStar_List.zip names1 uu____67443  in
              (uu____67433, uu____67435)  in
            (env2, uu____67420)
         in
      let extract_one_family env1 ind =
        let uu____67504 = binders_as_mlty_binders env1 ind.iparams  in
        match uu____67504 with
        | (env_iparams,vars) ->
            let uu____67548 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor env_iparams vars) env1)
               in
            (match uu____67548 with
             | (env2,ctors) ->
                 let uu____67655 = FStar_Syntax_Util.arrow_formals ind.ityp
                    in
                 (match uu____67655 with
                  | (indices,uu____67697) ->
                      let ml_params =
                        let uu____67722 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____67748  ->
                                    let uu____67756 =
                                      FStar_Util.string_of_int i  in
                                    Prims.op_Hat "'dummyV" uu____67756))
                           in
                        FStar_List.append vars uu____67722  in
                      let tbody =
                        let uu____67761 =
                          FStar_Util.find_opt
                            (fun uu___619_67766  ->
                               match uu___619_67766 with
                               | FStar_Syntax_Syntax.RecordType uu____67768
                                   -> true
                               | uu____67778 -> false) ind.iquals
                           in
                        match uu____67761 with
                        | FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                            let uu____67790 = FStar_List.hd ctors  in
                            (match uu____67790 with
                             | (uu____67815,c_ty) ->
                                 let fields =
                                   FStar_List.map2
                                     (fun id1  ->
                                        fun uu____67859  ->
                                          match uu____67859 with
                                          | (uu____67870,ty) ->
                                              let lid =
                                                FStar_Ident.lid_of_ids
                                                  (FStar_List.append ns [id1])
                                                 in
                                              let uu____67875 =
                                                lident_as_mlsymbol lid  in
                                              (uu____67875, ty)) ids c_ty
                                    in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____67878 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors
                         in
                      let uu____67881 =
                        let uu____67904 = lident_as_mlsymbol ind.iname  in
                        (false, uu____67904, FStar_Pervasives_Native.None,
                          ml_params, (ind.imetadata),
                          (FStar_Pervasives_Native.Some tbody))
                         in
                      (env2, uu____67881)))
         in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____67949,t,uu____67951,uu____67952,uu____67953);
            FStar_Syntax_Syntax.sigrng = uu____67954;
            FStar_Syntax_Syntax.sigquals = uu____67955;
            FStar_Syntax_Syntax.sigmeta = uu____67956;
            FStar_Syntax_Syntax.sigattrs = uu____67957;_}::[],uu____67958),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____67977 = extract_ctor env [] env { dname = l; dtyp = t }
             in
          (match uu____67977 with
           | (env1,ctor) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____68030),quals) ->
          let uu____68044 =
            bundle_as_inductive_families env ses quals
              se.FStar_Syntax_Syntax.sigattrs
             in
          (match uu____68044 with
           | (env1,ifams) ->
               let uu____68063 =
                 FStar_Util.fold_map extract_one_family env1 ifams  in
               (match uu____68063 with
                | (env2,td) -> (env2, [FStar_Extraction_ML_Syntax.MLM_Ty td])))
      | uu____68172 -> failwith "Unexpected signature element"
  
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
             let uu____68230 = FStar_Syntax_Util.head_and_args t  in
             match uu____68230 with
             | (head1,args) ->
                 let uu____68278 =
                   let uu____68280 =
                     FStar_Syntax_Util.is_fvar FStar_Parser_Const.plugin_attr
                       head1
                      in
                   Prims.op_Negation uu____68280  in
                 if uu____68278
                 then FStar_Pervasives_Native.None
                 else
                   (match args with
                    | ({
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_int (s,uu____68299));
                         FStar_Syntax_Syntax.pos = uu____68300;
                         FStar_Syntax_Syntax.vars = uu____68301;_},uu____68302)::[]
                        ->
                        let uu____68341 =
                          let uu____68345 = FStar_Util.int_of_string s  in
                          FStar_Pervasives_Native.Some uu____68345  in
                        FStar_Pervasives_Native.Some uu____68341
                    | uu____68351 ->
                        FStar_Pervasives_Native.Some
                          FStar_Pervasives_Native.None))
         in
      let uu____68366 =
        let uu____68368 = FStar_Options.codegen ()  in
        uu____68368 <> (FStar_Pervasives_Native.Some FStar_Options.Plugin)
         in
      if uu____68366
      then []
      else
        (let uu____68378 = plugin_with_arity se.FStar_Syntax_Syntax.sigattrs
            in
         match uu____68378 with
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
                      let uu____68420 =
                        let uu____68421 = FStar_Ident.string_of_lid fv_lid1
                           in
                        FStar_Extraction_ML_Syntax.MLC_String uu____68421  in
                      FStar_Extraction_ML_Syntax.MLE_Const uu____68420  in
                    let uu____68423 =
                      FStar_Extraction_ML_Util.interpret_plugin_as_term_fun
                        g.FStar_Extraction_ML_UEnv.env_tcenv fv fv_t
                        arity_opt ml_name_str
                       in
                    match uu____68423 with
                    | FStar_Pervasives_Native.Some
                        (interp,nbe_interp,arity,plugin1) ->
                        let uu____68456 =
                          if plugin1
                          then
                            ("FStar_Tactics_Native.register_plugin",
                              [interp; nbe_interp])
                          else
                            ("FStar_Tactics_Native.register_tactic",
                              [interp])
                           in
                        (match uu____68456 with
                         | (register,args) ->
                             let h =
                               let uu____68493 =
                                 let uu____68494 =
                                   let uu____68495 =
                                     FStar_Ident.lid_of_str register  in
                                   FStar_Extraction_ML_Syntax.mlpath_of_lident
                                     uu____68495
                                    in
                                 FStar_Extraction_ML_Syntax.MLE_Name
                                   uu____68494
                                  in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    FStar_Extraction_ML_Syntax.MLTY_Top)
                                 uu____68493
                                in
                             let arity1 =
                               let uu____68497 =
                                 let uu____68498 =
                                   let uu____68510 =
                                     FStar_Util.string_of_int arity  in
                                   (uu____68510,
                                     FStar_Pervasives_Native.None)
                                    in
                                 FStar_Extraction_ML_Syntax.MLC_Int
                                   uu____68498
                                  in
                               FStar_Extraction_ML_Syntax.MLE_Const
                                 uu____68497
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
              | uu____68539 -> []))
  
let rec (extract_sig :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list))
  =
  fun g  ->
    fun se  ->
      FStar_Extraction_ML_UEnv.debug g
        (fun u  ->
           let uu____68567 = FStar_Syntax_Print.sigelt_to_string se  in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____68567);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle uu____68576 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____68585 ->
           extract_bundle g se
       | FStar_Syntax_Syntax.Sig_datacon uu____68602 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           FStar_TypeChecker_Env.is_reifiable_effect
             g.FStar_Extraction_ML_UEnv.env_tcenv
             ed.FStar_Syntax_Syntax.mname
           ->
           let uu____68619 = extract_reifiable_effect g ed  in
           (match uu____68619 with | (env,_iface,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_splice uu____68643 ->
           failwith "impossible: trying to extract splice"
       | FStar_Syntax_Syntax.Sig_new_effect uu____68657 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let uu____68663 =
             extract_type_declaration g lid se.FStar_Syntax_Syntax.sigquals
               se.FStar_Syntax_Syntax.sigattrs univs1 t
              in
           (match uu____68663 with | (env,uu____68679,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____68688) when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let uu____68697 =
             extract_typ_abbrev g se.FStar_Syntax_Syntax.sigquals
               se.FStar_Syntax_Syntax.sigattrs lb
              in
           (match uu____68697 with | (env,uu____68713,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____68722) ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____68733 =
             let uu____68742 =
               FStar_Syntax_Util.extract_attr'
                 FStar_Parser_Const.postprocess_extr_with attrs
                in
             match uu____68742 with
             | FStar_Pervasives_Native.None  ->
                 (attrs, FStar_Pervasives_Native.None)
             | FStar_Pervasives_Native.Some
                 (ats,(tau,FStar_Pervasives_Native.None )::uu____68771) ->
                 (ats, (FStar_Pervasives_Native.Some tau))
             | FStar_Pervasives_Native.Some (ats,args) ->
                 (FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng
                    (FStar_Errors.Warning_UnrecognizedAttribute,
                      "Ill-formed application of `postprocess_for_extraction_with`");
                  (attrs, FStar_Pervasives_Native.None))
              in
           (match uu____68733 with
            | (attrs1,post_tau) ->
                let postprocess_lb tau lb =
                  let lbdef =
                    FStar_TypeChecker_Env.postprocess
                      g.FStar_Extraction_ML_UEnv.env_tcenv tau
                      lb.FStar_Syntax_Syntax.lbtyp
                      lb.FStar_Syntax_Syntax.lbdef
                     in
                  let uu___1403_68857 = lb  in
                  {
                    FStar_Syntax_Syntax.lbname =
                      (uu___1403_68857.FStar_Syntax_Syntax.lbname);
                    FStar_Syntax_Syntax.lbunivs =
                      (uu___1403_68857.FStar_Syntax_Syntax.lbunivs);
                    FStar_Syntax_Syntax.lbtyp =
                      (uu___1403_68857.FStar_Syntax_Syntax.lbtyp);
                    FStar_Syntax_Syntax.lbeff =
                      (uu___1403_68857.FStar_Syntax_Syntax.lbeff);
                    FStar_Syntax_Syntax.lbdef = lbdef;
                    FStar_Syntax_Syntax.lbattrs =
                      (uu___1403_68857.FStar_Syntax_Syntax.lbattrs);
                    FStar_Syntax_Syntax.lbpos =
                      (uu___1403_68857.FStar_Syntax_Syntax.lbpos)
                  }  in
                let lbs1 =
                  let uu____68866 =
                    match post_tau with
                    | FStar_Pervasives_Native.Some tau ->
                        FStar_List.map (postprocess_lb tau)
                          (FStar_Pervasives_Native.snd lbs)
                    | FStar_Pervasives_Native.None  ->
                        FStar_Pervasives_Native.snd lbs
                     in
                  ((FStar_Pervasives_Native.fst lbs), uu____68866)  in
                let uu____68884 =
                  let uu____68891 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_let
                         (lbs1, FStar_Syntax_Util.exp_false_bool))
                      FStar_Pervasives_Native.None
                      se.FStar_Syntax_Syntax.sigrng
                     in
                  FStar_Extraction_ML_Term.term_as_mlexpr g uu____68891  in
                (match uu____68884 with
                 | (ml_let,uu____68908,uu____68909) ->
                     (match ml_let.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Let
                          ((flavor,bindings),uu____68918) ->
                          let flags = FStar_List.choose flag_of_qual quals
                             in
                          let flags' = extract_metadata attrs1  in
                          let uu____68935 =
                            FStar_List.fold_left2
                              (fun uu____68961  ->
                                 fun ml_lb  ->
                                   fun uu____68963  ->
                                     match (uu____68961, uu____68963) with
                                     | ((env,ml_lbs),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbname;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uu____68985;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = t;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____68987;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = uu____68988;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____68989;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____68990;_})
                                         ->
                                         let uu____69015 =
                                           FStar_All.pipe_right
                                             ml_lb.FStar_Extraction_ML_Syntax.mllb_meta
                                             (FStar_List.contains
                                                FStar_Extraction_ML_Syntax.Erased)
                                            in
                                         if uu____69015
                                         then (env, ml_lbs)
                                         else
                                           (let lb_lid =
                                              let uu____69032 =
                                                let uu____69035 =
                                                  FStar_Util.right lbname  in
                                                uu____69035.FStar_Syntax_Syntax.fv_name
                                                 in
                                              uu____69032.FStar_Syntax_Syntax.v
                                               in
                                            let flags'' =
                                              let uu____69039 =
                                                let uu____69040 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____69040.FStar_Syntax_Syntax.n
                                                 in
                                              match uu____69039 with
                                              | FStar_Syntax_Syntax.Tm_arrow
                                                  (uu____69045,{
                                                                 FStar_Syntax_Syntax.n
                                                                   =
                                                                   FStar_Syntax_Syntax.Comp
                                                                   {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____69046;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    = e;
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    =
                                                                    uu____69048;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____69049;
                                                                    FStar_Syntax_Syntax.flags
                                                                    =
                                                                    uu____69050;_};
                                                                 FStar_Syntax_Syntax.pos
                                                                   =
                                                                   uu____69051;
                                                                 FStar_Syntax_Syntax.vars
                                                                   =
                                                                   uu____69052;_})
                                                  when
                                                  let uu____69087 =
                                                    FStar_Ident.string_of_lid
                                                      e
                                                     in
                                                  uu____69087 =
                                                    "FStar.HyperStack.ST.StackInline"
                                                  ->
                                                  [FStar_Extraction_ML_Syntax.StackInline]
                                              | uu____69091 -> []  in
                                            let meta =
                                              FStar_List.append flags
                                                (FStar_List.append flags'
                                                   flags'')
                                               in
                                            let ml_lb1 =
                                              let uu___1451_69096 = ml_lb  in
                                              {
                                                FStar_Extraction_ML_Syntax.mllb_name
                                                  =
                                                  (uu___1451_69096.FStar_Extraction_ML_Syntax.mllb_name);
                                                FStar_Extraction_ML_Syntax.mllb_tysc
                                                  =
                                                  (uu___1451_69096.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                FStar_Extraction_ML_Syntax.mllb_add_unit
                                                  =
                                                  (uu___1451_69096.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                FStar_Extraction_ML_Syntax.mllb_def
                                                  =
                                                  (uu___1451_69096.FStar_Extraction_ML_Syntax.mllb_def);
                                                FStar_Extraction_ML_Syntax.mllb_meta
                                                  = meta;
                                                FStar_Extraction_ML_Syntax.print_typ
                                                  =
                                                  (uu___1451_69096.FStar_Extraction_ML_Syntax.print_typ)
                                              }  in
                                            let uu____69097 =
                                              let uu____69102 =
                                                FStar_All.pipe_right quals
                                                  (FStar_Util.for_some
                                                     (fun uu___620_69109  ->
                                                        match uu___620_69109
                                                        with
                                                        | FStar_Syntax_Syntax.Projector
                                                            uu____69111 ->
                                                            true
                                                        | uu____69117 ->
                                                            false))
                                                 in
                                              if uu____69102
                                              then
                                                let mname =
                                                  let uu____69133 =
                                                    mangle_projector_lid
                                                      lb_lid
                                                     in
                                                  FStar_All.pipe_right
                                                    uu____69133
                                                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                                                   in
                                                let uu____69142 =
                                                  let uu____69150 =
                                                    FStar_Util.right lbname
                                                     in
                                                  let uu____69151 =
                                                    FStar_Util.must
                                                      ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc
                                                     in
                                                  FStar_Extraction_ML_UEnv.extend_fv'
                                                    env uu____69150 mname
                                                    uu____69151
                                                    ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                                    false
                                                   in
                                                match uu____69142 with
                                                | (env1,uu____69158,uu____69159)
                                                    ->
                                                    (env1,
                                                      (let uu___1464_69163 =
                                                         ml_lb1  in
                                                       {
                                                         FStar_Extraction_ML_Syntax.mllb_name
                                                           =
                                                           (FStar_Pervasives_Native.snd
                                                              mname);
                                                         FStar_Extraction_ML_Syntax.mllb_tysc
                                                           =
                                                           (uu___1464_69163.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                         FStar_Extraction_ML_Syntax.mllb_add_unit
                                                           =
                                                           (uu___1464_69163.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                         FStar_Extraction_ML_Syntax.mllb_def
                                                           =
                                                           (uu___1464_69163.FStar_Extraction_ML_Syntax.mllb_def);
                                                         FStar_Extraction_ML_Syntax.mllb_meta
                                                           =
                                                           (uu___1464_69163.FStar_Extraction_ML_Syntax.mllb_meta);
                                                         FStar_Extraction_ML_Syntax.print_typ
                                                           =
                                                           (uu___1464_69163.FStar_Extraction_ML_Syntax.print_typ)
                                                       }))
                                              else
                                                (let uu____69170 =
                                                   let uu____69178 =
                                                     FStar_Util.must
                                                       ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc
                                                      in
                                                   FStar_Extraction_ML_UEnv.extend_lb
                                                     env lbname t uu____69178
                                                     ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                                     false
                                                    in
                                                 match uu____69170 with
                                                 | (env1,uu____69185,uu____69186)
                                                     -> (env1, ml_lb1))
                                               in
                                            match uu____69097 with
                                            | (g1,ml_lb2) ->
                                                (g1, (ml_lb2 :: ml_lbs))))
                              (g, []) bindings
                              (FStar_Pervasives_Native.snd lbs1)
                             in
                          (match uu____68935 with
                           | (g1,ml_lbs') ->
                               let uu____69216 =
                                 let uu____69219 =
                                   let uu____69222 =
                                     let uu____69223 =
                                       FStar_Extraction_ML_Util.mlloc_of_range
                                         se.FStar_Syntax_Syntax.sigrng
                                        in
                                     FStar_Extraction_ML_Syntax.MLM_Loc
                                       uu____69223
                                      in
                                   [uu____69222;
                                   FStar_Extraction_ML_Syntax.MLM_Let
                                     (flavor, (FStar_List.rev ml_lbs'))]
                                    in
                                 let uu____69226 =
                                   maybe_register_plugin g1 se  in
                                 FStar_List.append uu____69219 uu____69226
                                  in
                               (g1, uu____69216))
                      | uu____69231 ->
                          let uu____69232 =
                            let uu____69234 =
                              FStar_Extraction_ML_Code.string_of_mlexpr
                                g.FStar_Extraction_ML_UEnv.currentModule
                                ml_let
                               in
                            FStar_Util.format1
                              "Impossible: Translated a let to a non-let: %s"
                              uu____69234
                             in
                          failwith uu____69232)))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____69244,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____69249 =
             (FStar_All.pipe_right quals
                (FStar_List.contains FStar_Syntax_Syntax.Assumption))
               &&
               (let uu____69255 =
                  FStar_TypeChecker_Util.must_erase_for_extraction
                    g.FStar_Extraction_ML_UEnv.env_tcenv t
                   in
                Prims.op_Negation uu____69255)
              in
           if uu____69249
           then
             let always_fail1 =
               let uu___1484_69265 = se  in
               let uu____69266 =
                 let uu____69267 =
                   let uu____69274 =
                     let uu____69275 =
                       let uu____69278 = always_fail lid t  in [uu____69278]
                        in
                     (false, uu____69275)  in
                   (uu____69274, [])  in
                 FStar_Syntax_Syntax.Sig_let uu____69267  in
               {
                 FStar_Syntax_Syntax.sigel = uu____69266;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___1484_69265.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___1484_69265.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___1484_69265.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___1484_69265.FStar_Syntax_Syntax.sigattrs)
               }  in
             let uu____69285 = extract_sig g always_fail1  in
             (match uu____69285 with
              | (g1,mlm) ->
                  let uu____69304 =
                    FStar_Util.find_map quals
                      (fun uu___621_69309  ->
                         match uu___621_69309 with
                         | FStar_Syntax_Syntax.Discriminator l ->
                             FStar_Pervasives_Native.Some l
                         | uu____69313 -> FStar_Pervasives_Native.None)
                     in
                  (match uu____69304 with
                   | FStar_Pervasives_Native.Some l ->
                       let uu____69321 =
                         let uu____69324 =
                           let uu____69325 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng
                              in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____69325  in
                         let uu____69326 =
                           let uu____69329 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l
                              in
                           [uu____69329]  in
                         uu____69324 :: uu____69326  in
                       (g1, uu____69321)
                   | uu____69332 ->
                       let uu____69335 =
                         FStar_Util.find_map quals
                           (fun uu___622_69341  ->
                              match uu___622_69341 with
                              | FStar_Syntax_Syntax.Projector (l,uu____69345)
                                  -> FStar_Pervasives_Native.Some l
                              | uu____69346 -> FStar_Pervasives_Native.None)
                          in
                       (match uu____69335 with
                        | FStar_Pervasives_Native.Some uu____69353 ->
                            (g1, [])
                        | uu____69356 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____69366 = FStar_Extraction_ML_Term.term_as_mlexpr g e  in
           (match uu____69366 with
            | (ml_main,uu____69380,uu____69381) ->
                let uu____69382 =
                  let uu____69385 =
                    let uu____69386 =
                      FStar_Extraction_ML_Util.mlloc_of_range
                        se.FStar_Syntax_Syntax.sigrng
                       in
                    FStar_Extraction_ML_Syntax.MLM_Loc uu____69386  in
                  [uu____69385; FStar_Extraction_ML_Syntax.MLM_Top ml_main]
                   in
                (g, uu____69382))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____69389 ->
           failwith "impossible -- removed by tc.fs"
       | FStar_Syntax_Syntax.Sig_assume uu____69397 -> (g, [])
       | FStar_Syntax_Syntax.Sig_sub_effect uu____69406 -> (g, [])
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____69409 -> (g, [])
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
      let uu____69451 = FStar_Options.restore_cmd_line_options true  in
      let name =
        FStar_Extraction_ML_Syntax.mlpath_of_lident
          m.FStar_Syntax_Syntax.name
         in
      let g1 =
        let uu___1527_69455 = g  in
        let uu____69456 =
          FStar_TypeChecker_Env.set_current_module
            g.FStar_Extraction_ML_UEnv.env_tcenv m.FStar_Syntax_Syntax.name
           in
        {
          FStar_Extraction_ML_UEnv.env_tcenv = uu____69456;
          FStar_Extraction_ML_UEnv.env_bindings =
            (uu___1527_69455.FStar_Extraction_ML_UEnv.env_bindings);
          FStar_Extraction_ML_UEnv.tydefs =
            (uu___1527_69455.FStar_Extraction_ML_UEnv.tydefs);
          FStar_Extraction_ML_UEnv.type_names =
            (uu___1527_69455.FStar_Extraction_ML_UEnv.type_names);
          FStar_Extraction_ML_UEnv.currentModule = name
        }  in
      let uu____69457 =
        FStar_Util.fold_map
          (fun g2  ->
             fun se  ->
               let uu____69476 =
                 FStar_Options.debug_module
                   (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                  in
               if uu____69476
               then
                 let nm =
                   let uu____69487 =
                     FStar_All.pipe_right
                       (FStar_Syntax_Util.lids_of_sigelt se)
                       (FStar_List.map FStar_Ident.string_of_lid)
                      in
                   FStar_All.pipe_right uu____69487
                     (FStar_String.concat ", ")
                    in
                 (FStar_Util.print1 "+++About to extract {%s}\n" nm;
                  (let uu____69504 =
                     FStar_Util.format1 "---Extracted {%s}" nm  in
                   FStar_Util.measure_execution_time uu____69504
                     (fun uu____69514  -> extract_sig g2 se)))
               else extract_sig g2 se) g1 m.FStar_Syntax_Syntax.declarations
         in
      match uu____69457 with
      | (g2,sigs) ->
          let mlm = FStar_List.flatten sigs  in
          let is_kremlin =
            let uu____69536 = FStar_Options.codegen ()  in
            uu____69536 =
              (FStar_Pervasives_Native.Some FStar_Options.Kremlin)
             in
          if
            ((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims") &&
              (is_kremlin ||
                 (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface))
          then
            ((let uu____69551 =
                let uu____69553 = FStar_Options.silent ()  in
                Prims.op_Negation uu____69553  in
              if uu____69551
              then
                let uu____69556 =
                  FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
                FStar_Util.print1 "Extracted module %s\n" uu____69556
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
      (let uu____69631 = FStar_Options.restore_cmd_line_options true  in
       FStar_All.pipe_left (fun a2  -> ()) uu____69631);
      (let uu____69634 =
         let uu____69636 =
           FStar_Options.should_extract
             (m.FStar_Syntax_Syntax.name).FStar_Ident.str
            in
         Prims.op_Negation uu____69636  in
       if uu____69634
       then
         let uu____69639 =
           let uu____69641 =
             FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
           FStar_Util.format1
             "Extract called on a module %s that should not be extracted"
             uu____69641
            in
         failwith uu____69639
       else ());
      (let uu____69646 = FStar_Options.interactive ()  in
       if uu____69646
       then (g, FStar_Pervasives_Native.None)
       else
         (let res =
            let uu____69666 = FStar_Options.debug_any ()  in
            if uu____69666
            then
              let msg =
                let uu____69677 =
                  FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name
                   in
                FStar_Util.format1 "Extracting module %s\n" uu____69677  in
              FStar_Util.measure_execution_time msg
                (fun uu____69687  -> extract' g m)
            else extract' g m  in
          (let uu____69691 = FStar_Options.restore_cmd_line_options true  in
           FStar_All.pipe_left (fun a3  -> ()) uu____69691);
          res))
  
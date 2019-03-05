open Prims
type env_t = FStar_Extraction_ML_UEnv.uenv
let (fail_exp :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun lid  ->
    fun t  ->
      let uu____68714 =
        let uu____68721 =
          let uu____68722 =
            let uu____68739 =
              FStar_Syntax_Syntax.fvar FStar_Parser_Const.failwith_lid
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            let uu____68742 =
              let uu____68753 = FStar_Syntax_Syntax.iarg t  in
              let uu____68762 =
                let uu____68773 =
                  let uu____68782 =
                    let uu____68783 =
                      let uu____68790 =
                        let uu____68791 =
                          let uu____68792 =
                            let uu____68798 =
                              let uu____68800 =
                                FStar_Syntax_Print.lid_to_string lid  in
                              Prims.op_Hat "Not yet implemented:" uu____68800
                               in
                            (uu____68798, FStar_Range.dummyRange)  in
                          FStar_Const.Const_string uu____68792  in
                        FStar_Syntax_Syntax.Tm_constant uu____68791  in
                      FStar_Syntax_Syntax.mk uu____68790  in
                    uu____68783 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange
                     in
                  FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____68782
                   in
                [uu____68773]  in
              uu____68753 :: uu____68762  in
            (uu____68739, uu____68742)  in
          FStar_Syntax_Syntax.Tm_app uu____68722  in
        FStar_Syntax_Syntax.mk uu____68721  in
      uu____68714 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (always_fail :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.letbinding)
  =
  fun lid  ->
    fun t  ->
      let imp =
        let uu____68872 = FStar_Syntax_Util.arrow_formals t  in
        match uu____68872 with
        | ([],t1) ->
            let b =
              let uu____68915 =
                FStar_Syntax_Syntax.gen_bv "_" FStar_Pervasives_Native.None
                  t1
                 in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____68915
               in
            let uu____68923 = fail_exp lid t1  in
            FStar_Syntax_Util.abs [b] uu____68923
              FStar_Pervasives_Native.None
        | (bs,t1) ->
            let uu____68960 = fail_exp lid t1  in
            FStar_Syntax_Util.abs bs uu____68960 FStar_Pervasives_Native.None
         in
      let lb =
        let uu____68964 =
          let uu____68969 =
            FStar_Syntax_Syntax.lid_as_fv lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Util.Inr uu____68969  in
        {
          FStar_Syntax_Syntax.lbname = uu____68964;
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
  'Auu____68991 . 'Auu____68991 Prims.list -> ('Auu____68991 * 'Auu____68991)
  =
  fun uu___612_69002  ->
    match uu___612_69002 with
    | a::b::[] -> (a, b)
    | uu____69007 -> failwith "Expected a list with 2 elements"
  
let (flag_of_qual :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option)
  =
  fun uu___613_69022  ->
    match uu___613_69022 with
    | FStar_Syntax_Syntax.Assumption  ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Assumed
    | FStar_Syntax_Syntax.Private  ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Private
    | FStar_Syntax_Syntax.NoExtract  ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.NoExtract
    | uu____69025 -> FStar_Pervasives_Native.None
  
let rec (extract_meta :
  FStar_Syntax_Syntax.term ->
    FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option)
  =
  fun x  ->
    let uu____69034 = FStar_Syntax_Subst.compress x  in
    match uu____69034 with
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
        FStar_Syntax_Syntax.pos = uu____69038;
        FStar_Syntax_Syntax.vars = uu____69039;_} ->
        let uu____69042 =
          let uu____69044 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____69044  in
        (match uu____69042 with
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
         | uu____69054 -> FStar_Pervasives_Native.None)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____69057;
             FStar_Syntax_Syntax.vars = uu____69058;_},({
                                                          FStar_Syntax_Syntax.n
                                                            =
                                                            FStar_Syntax_Syntax.Tm_constant
                                                            (FStar_Const.Const_string
                                                            (s,uu____69060));
                                                          FStar_Syntax_Syntax.pos
                                                            = uu____69061;
                                                          FStar_Syntax_Syntax.vars
                                                            = uu____69062;_},uu____69063)::[]);
        FStar_Syntax_Syntax.pos = uu____69064;
        FStar_Syntax_Syntax.vars = uu____69065;_} ->
        let uu____69108 =
          let uu____69110 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____69110  in
        (match uu____69108 with
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
         | uu____69119 -> FStar_Pervasives_Native.None)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("KremlinPrivate",uu____69121));
        FStar_Syntax_Syntax.pos = uu____69122;
        FStar_Syntax_Syntax.vars = uu____69123;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Private
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("c_inline",uu____69128));
        FStar_Syntax_Syntax.pos = uu____69129;
        FStar_Syntax_Syntax.vars = uu____69130;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.CInline
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("substitute",uu____69135));
        FStar_Syntax_Syntax.pos = uu____69136;
        FStar_Syntax_Syntax.vars = uu____69137;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Substitute
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_meta (x1,uu____69143);
        FStar_Syntax_Syntax.pos = uu____69144;
        FStar_Syntax_Syntax.vars = uu____69145;_} -> extract_meta x1
    | uu____69152 -> FStar_Pervasives_Native.None
  
let (extract_metadata :
  FStar_Syntax_Syntax.term Prims.list ->
    FStar_Extraction_ML_Syntax.meta Prims.list)
  = fun metas  -> FStar_List.choose extract_meta metas 
let binders_as_mlty_binders :
  'Auu____69172 .
    FStar_Extraction_ML_UEnv.uenv ->
      (FStar_Syntax_Syntax.bv * 'Auu____69172) Prims.list ->
        (FStar_Extraction_ML_UEnv.uenv * Prims.string Prims.list)
  =
  fun env  ->
    fun bs  ->
      FStar_Util.fold_map
        (fun env1  ->
           fun uu____69214  ->
             match uu____69214 with
             | (bv,uu____69225) ->
                 let uu____69226 =
                   let uu____69227 =
                     let uu____69230 =
                       let uu____69231 =
                         FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv  in
                       FStar_Extraction_ML_Syntax.MLTY_Var uu____69231  in
                     FStar_Pervasives_Native.Some uu____69230  in
                   FStar_Extraction_ML_UEnv.extend_ty env1 bv uu____69227  in
                 let uu____69233 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv
                    in
                 (uu____69226, uu____69233)) env bs
  
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
    let uu____69434 = FStar_Syntax_Print.lid_to_string i.iname  in
    let uu____69436 = FStar_Syntax_Print.binders_to_string " " i.iparams  in
    let uu____69439 = FStar_Syntax_Print.term_to_string i.ityp  in
    let uu____69441 =
      let uu____69443 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d  ->
                let uu____69457 = FStar_Syntax_Print.lid_to_string d.dname
                   in
                let uu____69459 =
                  let uu____69461 = FStar_Syntax_Print.term_to_string d.dtyp
                     in
                  Prims.op_Hat " : " uu____69461  in
                Prims.op_Hat uu____69457 uu____69459))
         in
      FStar_All.pipe_right uu____69443 (FStar_String.concat "\n\t\t")  in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____69434 uu____69436
      uu____69439 uu____69441
  
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
          let uu____69515 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun se  ->
                   match se.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,_us,bs,t,_mut_i,datas) ->
                       let uu____69563 = FStar_Syntax_Subst.open_term bs t
                          in
                       (match uu____69563 with
                        | (bs1,t1) ->
                            let datas1 =
                              FStar_All.pipe_right ses
                                (FStar_List.collect
                                   (fun se1  ->
                                      match se1.FStar_Syntax_Syntax.sigel
                                      with
                                      | FStar_Syntax_Syntax.Sig_datacon
                                          (d,uu____69602,t2,l',nparams,uu____69606)
                                          when FStar_Ident.lid_equals l l' ->
                                          let uu____69613 =
                                            FStar_Syntax_Util.arrow_formals
                                              t2
                                             in
                                          (match uu____69613 with
                                           | (bs',body) ->
                                               let uu____69652 =
                                                 FStar_Util.first_N
                                                   (FStar_List.length bs1)
                                                   bs'
                                                  in
                                               (match uu____69652 with
                                                | (bs_params,rest) ->
                                                    let subst1 =
                                                      FStar_List.map2
                                                        (fun uu____69743  ->
                                                           fun uu____69744 
                                                             ->
                                                             match (uu____69743,
                                                                    uu____69744)
                                                             with
                                                             | ((b',uu____69770),
                                                                (b,uu____69772))
                                                                 ->
                                                                 let uu____69793
                                                                   =
                                                                   let uu____69800
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    b  in
                                                                   (b',
                                                                    uu____69800)
                                                                    in
                                                                 FStar_Syntax_Syntax.NT
                                                                   uu____69793)
                                                        bs_params bs1
                                                       in
                                                    let t3 =
                                                      let uu____69806 =
                                                        let uu____69807 =
                                                          FStar_Syntax_Syntax.mk_Total
                                                            body
                                                           in
                                                        FStar_Syntax_Util.arrow
                                                          rest uu____69807
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____69806
                                                        (FStar_Syntax_Subst.subst
                                                           subst1)
                                                       in
                                                    [{ dname = d; dtyp = t3 }]))
                                      | uu____69810 -> []))
                               in
                            let metadata =
                              let uu____69814 =
                                extract_metadata
                                  (FStar_List.append
                                     se.FStar_Syntax_Syntax.sigattrs attrs)
                                 in
                              let uu____69817 =
                                FStar_List.choose flag_of_qual quals  in
                              FStar_List.append uu____69814 uu____69817  in
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
                   | uu____69824 -> (env1, [])) env ses
             in
          match uu____69515 with
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
    let uu___820_70004 = empty_iface  in
    {
      iface_module_name = (uu___820_70004.iface_module_name);
      iface_bindings = fvs;
      iface_tydefs = (uu___820_70004.iface_tydefs);
      iface_type_names = (uu___820_70004.iface_type_names)
    }
  
let (iface_of_tydefs : FStar_Extraction_ML_UEnv.tydef Prims.list -> iface) =
  fun tds  ->
    let uu___823_70015 = empty_iface  in
    let uu____70016 =
      FStar_List.map (fun td  -> td.FStar_Extraction_ML_UEnv.tydef_fv) tds
       in
    {
      iface_module_name = (uu___823_70015.iface_module_name);
      iface_bindings = (uu___823_70015.iface_bindings);
      iface_tydefs = tds;
      iface_type_names = uu____70016
    }
  
let (iface_of_type_names : FStar_Syntax_Syntax.fv Prims.list -> iface) =
  fun fvs  ->
    let uu___827_70031 = empty_iface  in
    {
      iface_module_name = (uu___827_70031.iface_module_name);
      iface_bindings = (uu___827_70031.iface_bindings);
      iface_tydefs = (uu___827_70031.iface_tydefs);
      iface_type_names = fvs
    }
  
let (iface_union : iface -> iface -> iface) =
  fun if1  ->
    fun if2  ->
      let uu____70043 =
        if if1.iface_module_name <> if1.iface_module_name
        then failwith "Union not defined"
        else if1.iface_module_name  in
      {
        iface_module_name = uu____70043;
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
  'Auu____70088 .
    FStar_Extraction_ML_Syntax.mlpath ->
      ('Auu____70088 * FStar_Extraction_ML_Syntax.mlty) -> Prims.string
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
      let uu____70120 =
        FStar_Extraction_ML_Code.string_of_mlexpr cm
          e.FStar_Extraction_ML_UEnv.exp_b_expr
         in
      let uu____70122 =
        tscheme_to_string cm e.FStar_Extraction_ML_UEnv.exp_b_tscheme  in
      let uu____70124 =
        FStar_Util.string_of_bool e.FStar_Extraction_ML_UEnv.exp_b_inst_ok
         in
      FStar_Util.format4
        "{\n\texp_b_name = %s\n\texp_b_expr = %s\n\texp_b_tscheme = %s\n\texp_b_is_rec = %s }"
        e.FStar_Extraction_ML_UEnv.exp_b_name uu____70120 uu____70122
        uu____70124
  
let (print_binding :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_UEnv.exp_binding) ->
      Prims.string)
  =
  fun cm  ->
    fun uu____70142  ->
      match uu____70142 with
      | (fv,exp_binding) ->
          let uu____70150 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____70152 = print_exp_binding cm exp_binding  in
          FStar_Util.format2 "(%s, %s)" uu____70150 uu____70152
  
let (print_tydef :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_UEnv.tydef -> Prims.string)
  =
  fun cm  ->
    fun tydef  ->
      let uu____70167 =
        FStar_Syntax_Print.fv_to_string
          tydef.FStar_Extraction_ML_UEnv.tydef_fv
         in
      let uu____70169 =
        tscheme_to_string cm tydef.FStar_Extraction_ML_UEnv.tydef_def  in
      FStar_Util.format2 "(%s, %s)" uu____70167 uu____70169
  
let (iface_to_string : iface -> Prims.string) =
  fun iface1  ->
    let cm = iface1.iface_module_name  in
    let print_type_name tn = FStar_Syntax_Print.fv_to_string tn  in
    let uu____70187 =
      let uu____70189 =
        FStar_List.map (print_binding cm) iface1.iface_bindings  in
      FStar_All.pipe_right uu____70189 (FStar_String.concat "\n")  in
    let uu____70203 =
      let uu____70205 = FStar_List.map (print_tydef cm) iface1.iface_tydefs
         in
      FStar_All.pipe_right uu____70205 (FStar_String.concat "\n")  in
    let uu____70215 =
      let uu____70217 =
        FStar_List.map print_type_name iface1.iface_type_names  in
      FStar_All.pipe_right uu____70217 (FStar_String.concat "\n")  in
    FStar_Util.format4
      "Interface %s = {\niface_bindings=\n%s;\n\niface_tydefs=\n%s;\n\niface_type_names=%s;\n}"
      (mlpath_to_string iface1.iface_module_name) uu____70187 uu____70203
      uu____70215
  
let (gamma_to_string : FStar_Extraction_ML_UEnv.uenv -> Prims.string) =
  fun env  ->
    let cm = env.FStar_Extraction_ML_UEnv.currentModule  in
    let gamma =
      FStar_List.collect
        (fun uu___614_70250  ->
           match uu___614_70250 with
           | FStar_Extraction_ML_UEnv.Fv (b,e) -> [(b, e)]
           | uu____70267 -> []) env.FStar_Extraction_ML_UEnv.env_bindings
       in
    let uu____70272 =
      let uu____70274 = FStar_List.map (print_binding cm) gamma  in
      FStar_All.pipe_right uu____70274 (FStar_String.concat "\n")  in
    FStar_Util.format1 "Gamma = {\n %s }" uu____70272
  
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
          let uu____70334 =
            let uu____70343 =
              FStar_TypeChecker_Env.open_universes_in
                env.FStar_Extraction_ML_UEnv.env_tcenv
                lb.FStar_Syntax_Syntax.lbunivs
                [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp]
               in
            match uu____70343 with
            | (tcenv,uu____70361,def_typ) ->
                let uu____70367 = as_pair def_typ  in (tcenv, uu____70367)
             in
          match uu____70334 with
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
                let uu____70398 =
                  let uu____70399 = FStar_Syntax_Subst.compress lbdef1  in
                  FStar_All.pipe_right uu____70399 FStar_Syntax_Util.unmeta
                   in
                FStar_All.pipe_right uu____70398 FStar_Syntax_Util.un_uinst
                 in
              let def1 =
                match def.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_abs uu____70407 ->
                    FStar_Extraction_ML_Term.normalize_abs def
                | uu____70426 -> def  in
              let uu____70427 =
                match def1.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____70438) ->
                    FStar_Syntax_Subst.open_term bs body
                | uu____70463 -> ([], def1)  in
              (match uu____70427 with
               | (bs,body) ->
                   let assumed =
                     FStar_Util.for_some
                       (fun uu___615_70483  ->
                          match uu___615_70483 with
                          | FStar_Syntax_Syntax.Assumption  -> true
                          | uu____70486 -> false) quals
                      in
                   let uu____70488 = binders_as_mlty_binders env bs  in
                   (match uu____70488 with
                    | (env1,ml_bs) ->
                        let body1 =
                          let uu____70515 =
                            FStar_Extraction_ML_Term.term_as_mlty env1 body
                             in
                          FStar_All.pipe_right uu____70515
                            (FStar_Extraction_ML_Util.eraseTypeDeep
                               (FStar_Extraction_ML_Util.udelta_unfold env1))
                           in
                        let mangled_projector =
                          let uu____70520 =
                            FStar_All.pipe_right quals
                              (FStar_Util.for_some
                                 (fun uu___616_70527  ->
                                    match uu___616_70527 with
                                    | FStar_Syntax_Syntax.Projector
                                        uu____70529 -> true
                                    | uu____70535 -> false))
                             in
                          if uu____70520
                          then
                            let mname = mangle_projector_lid lid  in
                            FStar_Pervasives_Native.Some
                              ((mname.FStar_Ident.ident).FStar_Ident.idText)
                          else FStar_Pervasives_Native.None  in
                        let metadata =
                          let uu____70549 = extract_metadata attrs  in
                          let uu____70552 =
                            FStar_List.choose flag_of_qual quals  in
                          FStar_List.append uu____70549 uu____70552  in
                        let td =
                          let uu____70575 = lident_as_mlsymbol lid  in
                          (assumed, uu____70575, mangled_projector, ml_bs,
                            metadata,
                            (FStar_Pervasives_Native.Some
                               (FStar_Extraction_ML_Syntax.MLTD_Abbrev body1)))
                           in
                        let def2 =
                          let uu____70587 =
                            let uu____70588 =
                              let uu____70589 = FStar_Ident.range_of_lid lid
                                 in
                              FStar_Extraction_ML_Util.mlloc_of_range
                                uu____70589
                               in
                            FStar_Extraction_ML_Syntax.MLM_Loc uu____70588
                             in
                          [uu____70587;
                          FStar_Extraction_ML_Syntax.MLM_Ty [td]]  in
                        let uu____70590 =
                          let uu____70595 =
                            FStar_All.pipe_right quals
                              (FStar_Util.for_some
                                 (fun uu___617_70601  ->
                                    match uu___617_70601 with
                                    | FStar_Syntax_Syntax.Assumption  -> true
                                    | FStar_Syntax_Syntax.New  -> true
                                    | uu____70605 -> false))
                             in
                          if uu____70595
                          then
                            let uu____70612 =
                              FStar_Extraction_ML_UEnv.extend_type_name env
                                fv
                               in
                            (uu____70612, (iface_of_type_names [fv]))
                          else
                            (let uu____70615 =
                               FStar_Extraction_ML_UEnv.extend_tydef env fv
                                 td
                                in
                             match uu____70615 with
                             | (env2,tydef) ->
                                 let uu____70626 = iface_of_tydefs [tydef]
                                    in
                                 (env2, uu____70626))
                           in
                        (match uu____70590 with
                         | (env2,iface1) -> (env2, iface1, def2))))
  
let (extract_bundle_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt -> (env_t * iface))
  =
  fun env  ->
    fun se  ->
      let extract_ctor env_iparams ml_tyvars env1 ctor =
        let mlt =
          let uu____70702 =
            FStar_Extraction_ML_Term.term_as_mlty env_iparams ctor.dtyp  in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env_iparams) uu____70702
           in
        let tys = (ml_tyvars, mlt)  in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp  in
        let uu____70709 =
          FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false  in
        match uu____70709 with | (env2,uu____70728,b) -> (env2, (fvv, b))  in
      let extract_one_family env1 ind =
        let uu____70767 = binders_as_mlty_binders env1 ind.iparams  in
        match uu____70767 with
        | (env_iparams,vars) ->
            let uu____70795 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor env_iparams vars) env1)
               in
            (match uu____70795 with | (env2,ctors) -> (env2, ctors))
         in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____70859,t,uu____70861,uu____70862,uu____70863);
            FStar_Syntax_Syntax.sigrng = uu____70864;
            FStar_Syntax_Syntax.sigquals = uu____70865;
            FStar_Syntax_Syntax.sigmeta = uu____70866;
            FStar_Syntax_Syntax.sigattrs = uu____70867;_}::[],uu____70868),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____70887 = extract_ctor env [] env { dname = l; dtyp = t }
             in
          (match uu____70887 with
           | (env1,ctor) -> (env1, (iface_of_bindings [ctor])))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____70920),quals) ->
          let uu____70934 =
            bundle_as_inductive_families env ses quals
              se.FStar_Syntax_Syntax.sigattrs
             in
          (match uu____70934 with
           | (env1,ifams) ->
               let uu____70951 =
                 FStar_Util.fold_map extract_one_family env1 ifams  in
               (match uu____70951 with
                | (env2,td) ->
                    let uu____70992 =
                      let uu____70993 =
                        let uu____70994 =
                          FStar_List.map (fun x  -> x.ifv) ifams  in
                        iface_of_type_names uu____70994  in
                      iface_union uu____70993
                        (iface_of_bindings (FStar_List.flatten td))
                       in
                    (env2, uu____70992)))
      | uu____71003 -> failwith "Unexpected signature element"
  
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
              let uu____71078 =
                let uu____71080 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun uu___618_71086  ->
                          match uu___618_71086 with
                          | FStar_Syntax_Syntax.Assumption  -> true
                          | uu____71089 -> false))
                   in
                Prims.op_Negation uu____71080  in
              if uu____71078
              then (g, empty_iface, [])
              else
                (let uu____71104 = FStar_Syntax_Util.arrow_formals t  in
                 match uu____71104 with
                 | (bs,uu____71128) ->
                     let fv =
                       FStar_Syntax_Syntax.lid_as_fv lid
                         FStar_Syntax_Syntax.delta_constant
                         FStar_Pervasives_Native.None
                        in
                     let lb =
                       let uu____71151 =
                         FStar_Syntax_Util.abs bs FStar_Syntax_Syntax.t_unit
                           FStar_Pervasives_Native.None
                          in
                       {
                         FStar_Syntax_Syntax.lbname = (FStar_Util.Inr fv);
                         FStar_Syntax_Syntax.lbunivs = univs1;
                         FStar_Syntax_Syntax.lbtyp = t;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_Tot_lid;
                         FStar_Syntax_Syntax.lbdef = uu____71151;
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
        let uu____71214 =
          FStar_Extraction_ML_UEnv.extend_fv' g1 fv ml_name tysc false false
           in
        match uu____71214 with
        | (g2,mangled_name,exp_binding) ->
            ((let uu____71236 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g2.FStar_Extraction_ML_UEnv.env_tcenv)
                  (FStar_Options.Other "ExtractionReify")
                 in
              if uu____71236
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
        (let uu____71272 =
           FStar_All.pipe_left
             (FStar_TypeChecker_Env.debug
                g.FStar_Extraction_ML_UEnv.env_tcenv)
             (FStar_Options.Other "ExtractionReify")
            in
         if uu____71272
         then
           let uu____71277 = FStar_Syntax_Print.term_to_string tm  in
           FStar_Util.print1 "extract_fv term: %s\n" uu____71277
         else ());
        (let uu____71282 =
           let uu____71283 = FStar_Syntax_Subst.compress tm  in
           uu____71283.FStar_Syntax_Syntax.n  in
         match uu____71282 with
         | FStar_Syntax_Syntax.Tm_uinst (tm1,uu____71291) -> extract_fv tm1
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             let mlp =
               FStar_Extraction_ML_Syntax.mlpath_of_lident
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             let uu____71298 = FStar_Extraction_ML_UEnv.lookup_fv g fv  in
             (match uu____71298 with
              | { FStar_Extraction_ML_UEnv.exp_b_name = uu____71303;
                  FStar_Extraction_ML_UEnv.exp_b_expr = uu____71304;
                  FStar_Extraction_ML_UEnv.exp_b_tscheme = tysc;
                  FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____71306;_} ->
                  let uu____71309 =
                    FStar_All.pipe_left
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.MLTY_Top)
                      (FStar_Extraction_ML_Syntax.MLE_Name mlp)
                     in
                  (uu____71309, tysc))
         | uu____71310 ->
             let uu____71311 =
               let uu____71313 =
                 FStar_Range.string_of_range tm.FStar_Syntax_Syntax.pos  in
               let uu____71315 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.format2 "(%s) Not an fv: %s" uu____71313
                 uu____71315
                in
             failwith uu____71311)
         in
      let extract_action g1 a =
        (let uu____71343 =
           FStar_All.pipe_left
             (FStar_TypeChecker_Env.debug
                g1.FStar_Extraction_ML_UEnv.env_tcenv)
             (FStar_Options.Other "ExtractionReify")
            in
         if uu____71343
         then
           let uu____71348 =
             FStar_Syntax_Print.term_to_string
               a.FStar_Syntax_Syntax.action_typ
              in
           let uu____71350 =
             FStar_Syntax_Print.term_to_string
               a.FStar_Syntax_Syntax.action_defn
              in
           FStar_Util.print2 "Action type %s and term %s\n" uu____71348
             uu____71350
         else ());
        (let uu____71355 = FStar_Extraction_ML_UEnv.action_name ed a  in
         match uu____71355 with
         | (a_nm,a_lid) ->
             let lbname =
               let uu____71375 =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some
                      ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                   FStar_Syntax_Syntax.tun
                  in
               FStar_Util.Inl uu____71375  in
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
             let uu____71405 =
               FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb  in
             (match uu____71405 with
              | (a_let,uu____71421,ty) ->
                  ((let uu____71424 =
                      FStar_All.pipe_left
                        (FStar_TypeChecker_Env.debug
                           g1.FStar_Extraction_ML_UEnv.env_tcenv)
                        (FStar_Options.Other "ExtractionReify")
                       in
                    if uu____71424
                    then
                      let uu____71429 =
                        FStar_Extraction_ML_Code.string_of_mlexpr a_nm a_let
                         in
                      FStar_Util.print1 "Extracted action term: %s\n"
                        uu____71429
                    else ());
                   (let uu____71434 =
                      match a_let.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Let
                          ((uu____71457,mllb::[]),uu____71459) ->
                          (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc
                           with
                           | FStar_Pervasives_Native.Some tysc ->
                               ((mllb.FStar_Extraction_ML_Syntax.mllb_def),
                                 tysc)
                           | FStar_Pervasives_Native.None  ->
                               failwith "No type scheme")
                      | uu____71499 -> failwith "Impossible"  in
                    match uu____71434 with
                    | (exp,tysc) ->
                        ((let uu____71537 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug
                                 g1.FStar_Extraction_ML_UEnv.env_tcenv)
                              (FStar_Options.Other "ExtractionReify")
                             in
                          if uu____71537
                          then
                            ((let uu____71543 =
                                FStar_Extraction_ML_Code.string_of_mlty a_nm
                                  (FStar_Pervasives_Native.snd tysc)
                                 in
                              FStar_Util.print1 "Extracted action type: %s\n"
                                uu____71543);
                             FStar_List.iter
                               (fun x  ->
                                  FStar_Util.print1 "and binders: %s\n" x)
                               (FStar_Pervasives_Native.fst tysc))
                          else ());
                         (let uu____71559 = extend_env g1 a_lid a_nm exp tysc
                             in
                          match uu____71559 with
                          | (env,iface1,impl) -> (env, (iface1, impl))))))))
         in
      let uu____71581 =
        let uu____71588 =
          extract_fv
            (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.return_repr)
           in
        match uu____71588 with
        | (return_tm,ty_sc) ->
            let uu____71605 =
              FStar_Extraction_ML_UEnv.monad_op_name ed "return"  in
            (match uu____71605 with
             | (return_nm,return_lid) ->
                 extend_env g return_lid return_nm return_tm ty_sc)
         in
      match uu____71581 with
      | (g1,return_iface,return_decl) ->
          let uu____71630 =
            let uu____71637 =
              extract_fv
                (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.bind_repr)
               in
            match uu____71637 with
            | (bind_tm,ty_sc) ->
                let uu____71654 =
                  FStar_Extraction_ML_UEnv.monad_op_name ed "bind"  in
                (match uu____71654 with
                 | (bind_nm,bind_lid) ->
                     extend_env g1 bind_lid bind_nm bind_tm ty_sc)
             in
          (match uu____71630 with
           | (g2,bind_iface,bind_decl) ->
               let uu____71679 =
                 FStar_Util.fold_map extract_action g2
                   ed.FStar_Syntax_Syntax.actions
                  in
               (match uu____71679 with
                | (g3,actions) ->
                    let uu____71716 = FStar_List.unzip actions  in
                    (match uu____71716 with
                     | (actions_iface,actions1) ->
                         let uu____71743 =
                           iface_union_l (return_iface :: bind_iface ::
                             actions_iface)
                            in
                         (g3, uu____71743, (return_decl :: bind_decl ::
                           actions1)))))
  
let (extract_sigelt_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle uu____71765 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____71774 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_datacon uu____71791 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) when
          FStar_Extraction_ML_Term.is_arity g t ->
          let uu____71810 =
            extract_type_declaration g lid se.FStar_Syntax_Syntax.sigquals
              se.FStar_Syntax_Syntax.sigattrs univs1 t
             in
          (match uu____71810 with | (env,iface1,uu____71825) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____71831) when
          FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp ->
          let uu____71840 =
            extract_typ_abbrev g se.FStar_Syntax_Syntax.sigquals
              se.FStar_Syntax_Syntax.sigattrs lb
             in
          (match uu____71840 with | (env,iface1,uu____71855) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,_univs,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let uu____71866 =
            (FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption))
              &&
              (let uu____71872 =
                 FStar_TypeChecker_Util.must_erase_for_extraction
                   g.FStar_Extraction_ML_UEnv.env_tcenv t
                  in
               Prims.op_Negation uu____71872)
             in
          if uu____71866
          then
            let uu____71879 =
              let uu____71890 =
                let uu____71891 =
                  let uu____71894 = always_fail lid t  in [uu____71894]  in
                (false, uu____71891)  in
              FStar_Extraction_ML_Term.extract_lb_iface g uu____71890  in
            (match uu____71879 with
             | (g1,bindings) -> (g1, (iface_of_bindings bindings)))
          else (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____71920) ->
          let uu____71925 = FStar_Extraction_ML_Term.extract_lb_iface g lbs
             in
          (match uu____71925 with
           | (g1,bindings) -> (g1, (iface_of_bindings bindings)))
      | FStar_Syntax_Syntax.Sig_main uu____71954 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____71955 ->
          (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_assume uu____71956 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____71963 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____71964 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          (FStar_Syntax_Util.process_pragma p se.FStar_Syntax_Syntax.sigrng;
           (g, empty_iface))
      | FStar_Syntax_Syntax.Sig_splice uu____71979 ->
          failwith "impossible: trying to extract splice"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____71992 =
            (FStar_TypeChecker_Env.is_reifiable_effect
               g.FStar_Extraction_ML_UEnv.env_tcenv
               ed.FStar_Syntax_Syntax.mname)
              && (FStar_List.isEmpty ed.FStar_Syntax_Syntax.binders)
             in
          if uu____71992
          then
            let uu____72005 = extract_reifiable_effect g ed  in
            (match uu____72005 with
             | (env,iface1,uu____72020) -> (env, iface1))
          else (g, empty_iface)
  
let (extract_iface' :
  env_t ->
    FStar_Syntax_Syntax.modul -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun modul  ->
      let uu____72042 = FStar_Options.interactive ()  in
      if uu____72042
      then (g, empty_iface)
      else
        (let uu____72051 = FStar_Options.restore_cmd_line_options true  in
         let decls = modul.FStar_Syntax_Syntax.declarations  in
         let iface1 =
           let uu___1166_72055 = empty_iface  in
           {
             iface_module_name = (g.FStar_Extraction_ML_UEnv.currentModule);
             iface_bindings = (uu___1166_72055.iface_bindings);
             iface_tydefs = (uu___1166_72055.iface_tydefs);
             iface_type_names = (uu___1166_72055.iface_type_names)
           }  in
         let res =
           FStar_List.fold_left
             (fun uu____72073  ->
                fun se  ->
                  match uu____72073 with
                  | (g1,iface2) ->
                      let uu____72085 = extract_sigelt_iface g1 se  in
                      (match uu____72085 with
                       | (g2,iface') ->
                           let uu____72096 = iface_union iface2 iface'  in
                           (g2, uu____72096))) (g, iface1) decls
            in
         (let uu____72098 = FStar_Options.restore_cmd_line_options true  in
          FStar_All.pipe_left (fun a1  -> ()) uu____72098);
         res)
  
let (extract_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.modul -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun modul  ->
      let uu____72115 = FStar_Options.debug_any ()  in
      if uu____72115
      then
        let uu____72122 =
          FStar_Util.format1 "Extracted interface of %s"
            (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
           in
        FStar_Util.measure_execution_time uu____72122
          (fun uu____72130  -> extract_iface' g modul)
      else extract_iface' g modul
  
let (extend_with_iface :
  FStar_Extraction_ML_UEnv.uenv -> iface -> FStar_Extraction_ML_UEnv.uenv) =
  fun g  ->
    fun iface1  ->
      let uu___1184_72144 = g  in
      let uu____72145 =
        let uu____72148 =
          FStar_List.map (fun _72155  -> FStar_Extraction_ML_UEnv.Fv _72155)
            iface1.iface_bindings
           in
        FStar_List.append uu____72148 g.FStar_Extraction_ML_UEnv.env_bindings
         in
      {
        FStar_Extraction_ML_UEnv.env_tcenv =
          (uu___1184_72144.FStar_Extraction_ML_UEnv.env_tcenv);
        FStar_Extraction_ML_UEnv.env_bindings = uu____72145;
        FStar_Extraction_ML_UEnv.tydefs =
          (FStar_List.append iface1.iface_tydefs
             g.FStar_Extraction_ML_UEnv.tydefs);
        FStar_Extraction_ML_UEnv.type_names =
          (FStar_List.append iface1.iface_type_names
             g.FStar_Extraction_ML_UEnv.type_names);
        FStar_Extraction_ML_UEnv.currentModule =
          (uu___1184_72144.FStar_Extraction_ML_UEnv.currentModule)
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
          let uu____72233 =
            FStar_Extraction_ML_Term.term_as_mlty env_iparams ctor.dtyp  in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env_iparams) uu____72233
           in
        let steps =
          [FStar_TypeChecker_Env.Inlining;
          FStar_TypeChecker_Env.UnfoldUntil
            FStar_Syntax_Syntax.delta_constant;
          FStar_TypeChecker_Env.EraseUniverses;
          FStar_TypeChecker_Env.AllowUnboundUniverses]  in
        let names1 =
          let uu____72241 =
            let uu____72242 =
              let uu____72245 =
                FStar_TypeChecker_Normalize.normalize steps
                  env_iparams.FStar_Extraction_ML_UEnv.env_tcenv ctor.dtyp
                 in
              FStar_Syntax_Subst.compress uu____72245  in
            uu____72242.FStar_Syntax_Syntax.n  in
          match uu____72241 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,uu____72250) ->
              FStar_List.map
                (fun uu____72283  ->
                   match uu____72283 with
                   | ({ FStar_Syntax_Syntax.ppname = ppname;
                        FStar_Syntax_Syntax.index = uu____72292;
                        FStar_Syntax_Syntax.sort = uu____72293;_},uu____72294)
                       -> ppname.FStar_Ident.idText) bs
          | uu____72302 -> []  in
        let tys = (ml_tyvars, mlt)  in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp  in
        let uu____72310 =
          FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false  in
        match uu____72310 with
        | (env2,uu____72337,uu____72338) ->
            let uu____72341 =
              let uu____72354 = lident_as_mlsymbol ctor.dname  in
              let uu____72356 =
                let uu____72364 = FStar_Extraction_ML_Util.argTypes mlt  in
                FStar_List.zip names1 uu____72364  in
              (uu____72354, uu____72356)  in
            (env2, uu____72341)
         in
      let extract_one_family env1 ind =
        let uu____72425 = binders_as_mlty_binders env1 ind.iparams  in
        match uu____72425 with
        | (env_iparams,vars) ->
            let uu____72469 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor env_iparams vars) env1)
               in
            (match uu____72469 with
             | (env2,ctors) ->
                 let uu____72576 = FStar_Syntax_Util.arrow_formals ind.ityp
                    in
                 (match uu____72576 with
                  | (indices,uu____72618) ->
                      let ml_params =
                        let uu____72643 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____72669  ->
                                    let uu____72677 =
                                      FStar_Util.string_of_int i  in
                                    Prims.op_Hat "'dummyV" uu____72677))
                           in
                        FStar_List.append vars uu____72643  in
                      let tbody =
                        let uu____72682 =
                          FStar_Util.find_opt
                            (fun uu___619_72687  ->
                               match uu___619_72687 with
                               | FStar_Syntax_Syntax.RecordType uu____72689
                                   -> true
                               | uu____72699 -> false) ind.iquals
                           in
                        match uu____72682 with
                        | FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                            let uu____72711 = FStar_List.hd ctors  in
                            (match uu____72711 with
                             | (uu____72736,c_ty) ->
                                 let fields =
                                   FStar_List.map2
                                     (fun id1  ->
                                        fun uu____72780  ->
                                          match uu____72780 with
                                          | (uu____72791,ty) ->
                                              let lid =
                                                FStar_Ident.lid_of_ids
                                                  (FStar_List.append ns [id1])
                                                 in
                                              let uu____72796 =
                                                lident_as_mlsymbol lid  in
                                              (uu____72796, ty)) ids c_ty
                                    in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____72799 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors
                         in
                      let uu____72802 =
                        let uu____72825 = lident_as_mlsymbol ind.iname  in
                        (false, uu____72825, FStar_Pervasives_Native.None,
                          ml_params, (ind.imetadata),
                          (FStar_Pervasives_Native.Some tbody))
                         in
                      (env2, uu____72802)))
         in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____72870,t,uu____72872,uu____72873,uu____72874);
            FStar_Syntax_Syntax.sigrng = uu____72875;
            FStar_Syntax_Syntax.sigquals = uu____72876;
            FStar_Syntax_Syntax.sigmeta = uu____72877;
            FStar_Syntax_Syntax.sigattrs = uu____72878;_}::[],uu____72879),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____72898 = extract_ctor env [] env { dname = l; dtyp = t }
             in
          (match uu____72898 with
           | (env1,ctor) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____72951),quals) ->
          let uu____72965 =
            bundle_as_inductive_families env ses quals
              se.FStar_Syntax_Syntax.sigattrs
             in
          (match uu____72965 with
           | (env1,ifams) ->
               let uu____72984 =
                 FStar_Util.fold_map extract_one_family env1 ifams  in
               (match uu____72984 with
                | (env2,td) -> (env2, [FStar_Extraction_ML_Syntax.MLM_Ty td])))
      | uu____73093 -> failwith "Unexpected signature element"
  
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
             let uu____73151 = FStar_Syntax_Util.head_and_args t  in
             match uu____73151 with
             | (head1,args) ->
                 let uu____73199 =
                   let uu____73201 =
                     FStar_Syntax_Util.is_fvar FStar_Parser_Const.plugin_attr
                       head1
                      in
                   Prims.op_Negation uu____73201  in
                 if uu____73199
                 then FStar_Pervasives_Native.None
                 else
                   (match args with
                    | ({
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_int (s,uu____73220));
                         FStar_Syntax_Syntax.pos = uu____73221;
                         FStar_Syntax_Syntax.vars = uu____73222;_},uu____73223)::[]
                        ->
                        let uu____73262 =
                          let uu____73266 = FStar_Util.int_of_string s  in
                          FStar_Pervasives_Native.Some uu____73266  in
                        FStar_Pervasives_Native.Some uu____73262
                    | uu____73272 ->
                        FStar_Pervasives_Native.Some
                          FStar_Pervasives_Native.None))
         in
      let uu____73287 =
        let uu____73289 = FStar_Options.codegen ()  in
        uu____73289 <> (FStar_Pervasives_Native.Some FStar_Options.Plugin)
         in
      if uu____73287
      then []
      else
        (let uu____73299 = plugin_with_arity se.FStar_Syntax_Syntax.sigattrs
            in
         match uu____73299 with
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
                      let uu____73341 =
                        let uu____73342 = FStar_Ident.string_of_lid fv_lid1
                           in
                        FStar_Extraction_ML_Syntax.MLC_String uu____73342  in
                      FStar_Extraction_ML_Syntax.MLE_Const uu____73341  in
                    let uu____73344 =
                      FStar_Extraction_ML_Util.interpret_plugin_as_term_fun
                        g.FStar_Extraction_ML_UEnv.env_tcenv fv fv_t
                        arity_opt ml_name_str
                       in
                    match uu____73344 with
                    | FStar_Pervasives_Native.Some
                        (interp,nbe_interp,arity,plugin1) ->
                        let uu____73377 =
                          if plugin1
                          then
                            ("FStar_Tactics_Native.register_plugin",
                              [interp; nbe_interp])
                          else
                            ("FStar_Tactics_Native.register_tactic",
                              [interp])
                           in
                        (match uu____73377 with
                         | (register,args) ->
                             let h =
                               let uu____73414 =
                                 let uu____73415 =
                                   let uu____73416 =
                                     FStar_Ident.lid_of_str register  in
                                   FStar_Extraction_ML_Syntax.mlpath_of_lident
                                     uu____73416
                                    in
                                 FStar_Extraction_ML_Syntax.MLE_Name
                                   uu____73415
                                  in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    FStar_Extraction_ML_Syntax.MLTY_Top)
                                 uu____73414
                                in
                             let arity1 =
                               let uu____73418 =
                                 let uu____73419 =
                                   let uu____73431 =
                                     FStar_Util.string_of_int arity  in
                                   (uu____73431,
                                     FStar_Pervasives_Native.None)
                                    in
                                 FStar_Extraction_ML_Syntax.MLC_Int
                                   uu____73419
                                  in
                               FStar_Extraction_ML_Syntax.MLE_Const
                                 uu____73418
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
              | uu____73460 -> []))
  
let rec (extract_sig :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list))
  =
  fun g  ->
    fun se  ->
      FStar_Extraction_ML_UEnv.debug g
        (fun u  ->
           let uu____73488 = FStar_Syntax_Print.sigelt_to_string se  in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____73488);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle uu____73497 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____73506 ->
           extract_bundle g se
       | FStar_Syntax_Syntax.Sig_datacon uu____73523 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           FStar_TypeChecker_Env.is_reifiable_effect
             g.FStar_Extraction_ML_UEnv.env_tcenv
             ed.FStar_Syntax_Syntax.mname
           ->
           let uu____73540 = extract_reifiable_effect g ed  in
           (match uu____73540 with | (env,_iface,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_splice uu____73564 ->
           failwith "impossible: trying to extract splice"
       | FStar_Syntax_Syntax.Sig_new_effect uu____73578 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let uu____73584 =
             extract_type_declaration g lid se.FStar_Syntax_Syntax.sigquals
               se.FStar_Syntax_Syntax.sigattrs univs1 t
              in
           (match uu____73584 with | (env,uu____73600,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____73609) when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let uu____73618 =
             extract_typ_abbrev g se.FStar_Syntax_Syntax.sigquals
               se.FStar_Syntax_Syntax.sigattrs lb
              in
           (match uu____73618 with | (env,uu____73634,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____73643) ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____73654 =
             let uu____73663 =
               FStar_Syntax_Util.extract_attr'
                 FStar_Parser_Const.postprocess_extr_with attrs
                in
             match uu____73663 with
             | FStar_Pervasives_Native.None  ->
                 (attrs, FStar_Pervasives_Native.None)
             | FStar_Pervasives_Native.Some
                 (ats,(tau,FStar_Pervasives_Native.None )::uu____73692) ->
                 (ats, (FStar_Pervasives_Native.Some tau))
             | FStar_Pervasives_Native.Some (ats,args) ->
                 (FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng
                    (FStar_Errors.Warning_UnrecognizedAttribute,
                      "Ill-formed application of `postprocess_for_extraction_with`");
                  (attrs, FStar_Pervasives_Native.None))
              in
           (match uu____73654 with
            | (attrs1,post_tau) ->
                let postprocess_lb tau lb =
                  let lbdef =
                    FStar_TypeChecker_Env.postprocess
                      g.FStar_Extraction_ML_UEnv.env_tcenv tau
                      lb.FStar_Syntax_Syntax.lbtyp
                      lb.FStar_Syntax_Syntax.lbdef
                     in
                  let uu___1403_73778 = lb  in
                  {
                    FStar_Syntax_Syntax.lbname =
                      (uu___1403_73778.FStar_Syntax_Syntax.lbname);
                    FStar_Syntax_Syntax.lbunivs =
                      (uu___1403_73778.FStar_Syntax_Syntax.lbunivs);
                    FStar_Syntax_Syntax.lbtyp =
                      (uu___1403_73778.FStar_Syntax_Syntax.lbtyp);
                    FStar_Syntax_Syntax.lbeff =
                      (uu___1403_73778.FStar_Syntax_Syntax.lbeff);
                    FStar_Syntax_Syntax.lbdef = lbdef;
                    FStar_Syntax_Syntax.lbattrs =
                      (uu___1403_73778.FStar_Syntax_Syntax.lbattrs);
                    FStar_Syntax_Syntax.lbpos =
                      (uu___1403_73778.FStar_Syntax_Syntax.lbpos)
                  }  in
                let lbs1 =
                  let uu____73787 =
                    match post_tau with
                    | FStar_Pervasives_Native.Some tau ->
                        FStar_List.map (postprocess_lb tau)
                          (FStar_Pervasives_Native.snd lbs)
                    | FStar_Pervasives_Native.None  ->
                        FStar_Pervasives_Native.snd lbs
                     in
                  ((FStar_Pervasives_Native.fst lbs), uu____73787)  in
                let uu____73805 =
                  let uu____73812 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_let
                         (lbs1, FStar_Syntax_Util.exp_false_bool))
                      FStar_Pervasives_Native.None
                      se.FStar_Syntax_Syntax.sigrng
                     in
                  FStar_Extraction_ML_Term.term_as_mlexpr g uu____73812  in
                (match uu____73805 with
                 | (ml_let,uu____73829,uu____73830) ->
                     (match ml_let.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Let
                          ((flavor,bindings),uu____73839) ->
                          let flags = FStar_List.choose flag_of_qual quals
                             in
                          let flags' = extract_metadata attrs1  in
                          let uu____73856 =
                            FStar_List.fold_left2
                              (fun uu____73882  ->
                                 fun ml_lb  ->
                                   fun uu____73884  ->
                                     match (uu____73882, uu____73884) with
                                     | ((env,ml_lbs),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbname;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uu____73906;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = t;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____73908;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = uu____73909;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____73910;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____73911;_})
                                         ->
                                         let uu____73936 =
                                           FStar_All.pipe_right
                                             ml_lb.FStar_Extraction_ML_Syntax.mllb_meta
                                             (FStar_List.contains
                                                FStar_Extraction_ML_Syntax.Erased)
                                            in
                                         if uu____73936
                                         then (env, ml_lbs)
                                         else
                                           (let lb_lid =
                                              let uu____73953 =
                                                let uu____73956 =
                                                  FStar_Util.right lbname  in
                                                uu____73956.FStar_Syntax_Syntax.fv_name
                                                 in
                                              uu____73953.FStar_Syntax_Syntax.v
                                               in
                                            let flags'' =
                                              let uu____73960 =
                                                let uu____73961 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____73961.FStar_Syntax_Syntax.n
                                                 in
                                              match uu____73960 with
                                              | FStar_Syntax_Syntax.Tm_arrow
                                                  (uu____73966,{
                                                                 FStar_Syntax_Syntax.n
                                                                   =
                                                                   FStar_Syntax_Syntax.Comp
                                                                   {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____73967;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    = e;
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    =
                                                                    uu____73969;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____73970;
                                                                    FStar_Syntax_Syntax.flags
                                                                    =
                                                                    uu____73971;_};
                                                                 FStar_Syntax_Syntax.pos
                                                                   =
                                                                   uu____73972;
                                                                 FStar_Syntax_Syntax.vars
                                                                   =
                                                                   uu____73973;_})
                                                  when
                                                  let uu____74008 =
                                                    FStar_Ident.string_of_lid
                                                      e
                                                     in
                                                  uu____74008 =
                                                    "FStar.HyperStack.ST.StackInline"
                                                  ->
                                                  [FStar_Extraction_ML_Syntax.StackInline]
                                              | uu____74012 -> []  in
                                            let meta =
                                              FStar_List.append flags
                                                (FStar_List.append flags'
                                                   flags'')
                                               in
                                            let ml_lb1 =
                                              let uu___1451_74017 = ml_lb  in
                                              {
                                                FStar_Extraction_ML_Syntax.mllb_name
                                                  =
                                                  (uu___1451_74017.FStar_Extraction_ML_Syntax.mllb_name);
                                                FStar_Extraction_ML_Syntax.mllb_tysc
                                                  =
                                                  (uu___1451_74017.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                FStar_Extraction_ML_Syntax.mllb_add_unit
                                                  =
                                                  (uu___1451_74017.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                FStar_Extraction_ML_Syntax.mllb_def
                                                  =
                                                  (uu___1451_74017.FStar_Extraction_ML_Syntax.mllb_def);
                                                FStar_Extraction_ML_Syntax.mllb_meta
                                                  = meta;
                                                FStar_Extraction_ML_Syntax.print_typ
                                                  =
                                                  (uu___1451_74017.FStar_Extraction_ML_Syntax.print_typ)
                                              }  in
                                            let uu____74018 =
                                              let uu____74023 =
                                                FStar_All.pipe_right quals
                                                  (FStar_Util.for_some
                                                     (fun uu___620_74030  ->
                                                        match uu___620_74030
                                                        with
                                                        | FStar_Syntax_Syntax.Projector
                                                            uu____74032 ->
                                                            true
                                                        | uu____74038 ->
                                                            false))
                                                 in
                                              if uu____74023
                                              then
                                                let mname =
                                                  let uu____74054 =
                                                    mangle_projector_lid
                                                      lb_lid
                                                     in
                                                  FStar_All.pipe_right
                                                    uu____74054
                                                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                                                   in
                                                let uu____74063 =
                                                  let uu____74071 =
                                                    FStar_Util.right lbname
                                                     in
                                                  let uu____74072 =
                                                    FStar_Util.must
                                                      ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc
                                                     in
                                                  FStar_Extraction_ML_UEnv.extend_fv'
                                                    env uu____74071 mname
                                                    uu____74072
                                                    ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                                    false
                                                   in
                                                match uu____74063 with
                                                | (env1,uu____74079,uu____74080)
                                                    ->
                                                    (env1,
                                                      (let uu___1464_74084 =
                                                         ml_lb1  in
                                                       {
                                                         FStar_Extraction_ML_Syntax.mllb_name
                                                           =
                                                           (FStar_Pervasives_Native.snd
                                                              mname);
                                                         FStar_Extraction_ML_Syntax.mllb_tysc
                                                           =
                                                           (uu___1464_74084.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                         FStar_Extraction_ML_Syntax.mllb_add_unit
                                                           =
                                                           (uu___1464_74084.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                         FStar_Extraction_ML_Syntax.mllb_def
                                                           =
                                                           (uu___1464_74084.FStar_Extraction_ML_Syntax.mllb_def);
                                                         FStar_Extraction_ML_Syntax.mllb_meta
                                                           =
                                                           (uu___1464_74084.FStar_Extraction_ML_Syntax.mllb_meta);
                                                         FStar_Extraction_ML_Syntax.print_typ
                                                           =
                                                           (uu___1464_74084.FStar_Extraction_ML_Syntax.print_typ)
                                                       }))
                                              else
                                                (let uu____74091 =
                                                   let uu____74099 =
                                                     FStar_Util.must
                                                       ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc
                                                      in
                                                   FStar_Extraction_ML_UEnv.extend_lb
                                                     env lbname t uu____74099
                                                     ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                                     false
                                                    in
                                                 match uu____74091 with
                                                 | (env1,uu____74106,uu____74107)
                                                     -> (env1, ml_lb1))
                                               in
                                            match uu____74018 with
                                            | (g1,ml_lb2) ->
                                                (g1, (ml_lb2 :: ml_lbs))))
                              (g, []) bindings
                              (FStar_Pervasives_Native.snd lbs1)
                             in
                          (match uu____73856 with
                           | (g1,ml_lbs') ->
                               let uu____74137 =
                                 let uu____74140 =
                                   let uu____74143 =
                                     let uu____74144 =
                                       FStar_Extraction_ML_Util.mlloc_of_range
                                         se.FStar_Syntax_Syntax.sigrng
                                        in
                                     FStar_Extraction_ML_Syntax.MLM_Loc
                                       uu____74144
                                      in
                                   [uu____74143;
                                   FStar_Extraction_ML_Syntax.MLM_Let
                                     (flavor, (FStar_List.rev ml_lbs'))]
                                    in
                                 let uu____74147 =
                                   maybe_register_plugin g1 se  in
                                 FStar_List.append uu____74140 uu____74147
                                  in
                               (g1, uu____74137))
                      | uu____74152 ->
                          let uu____74153 =
                            let uu____74155 =
                              FStar_Extraction_ML_Code.string_of_mlexpr
                                g.FStar_Extraction_ML_UEnv.currentModule
                                ml_let
                               in
                            FStar_Util.format1
                              "Impossible: Translated a let to a non-let: %s"
                              uu____74155
                             in
                          failwith uu____74153)))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____74165,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____74170 =
             (FStar_All.pipe_right quals
                (FStar_List.contains FStar_Syntax_Syntax.Assumption))
               &&
               (let uu____74176 =
                  FStar_TypeChecker_Util.must_erase_for_extraction
                    g.FStar_Extraction_ML_UEnv.env_tcenv t
                   in
                Prims.op_Negation uu____74176)
              in
           if uu____74170
           then
             let always_fail1 =
               let uu___1484_74186 = se  in
               let uu____74187 =
                 let uu____74188 =
                   let uu____74195 =
                     let uu____74196 =
                       let uu____74199 = always_fail lid t  in [uu____74199]
                        in
                     (false, uu____74196)  in
                   (uu____74195, [])  in
                 FStar_Syntax_Syntax.Sig_let uu____74188  in
               {
                 FStar_Syntax_Syntax.sigel = uu____74187;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___1484_74186.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___1484_74186.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___1484_74186.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___1484_74186.FStar_Syntax_Syntax.sigattrs)
               }  in
             let uu____74206 = extract_sig g always_fail1  in
             (match uu____74206 with
              | (g1,mlm) ->
                  let uu____74225 =
                    FStar_Util.find_map quals
                      (fun uu___621_74230  ->
                         match uu___621_74230 with
                         | FStar_Syntax_Syntax.Discriminator l ->
                             FStar_Pervasives_Native.Some l
                         | uu____74234 -> FStar_Pervasives_Native.None)
                     in
                  (match uu____74225 with
                   | FStar_Pervasives_Native.Some l ->
                       let uu____74242 =
                         let uu____74245 =
                           let uu____74246 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng
                              in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____74246  in
                         let uu____74247 =
                           let uu____74250 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l
                              in
                           [uu____74250]  in
                         uu____74245 :: uu____74247  in
                       (g1, uu____74242)
                   | uu____74253 ->
                       let uu____74256 =
                         FStar_Util.find_map quals
                           (fun uu___622_74262  ->
                              match uu___622_74262 with
                              | FStar_Syntax_Syntax.Projector (l,uu____74266)
                                  -> FStar_Pervasives_Native.Some l
                              | uu____74267 -> FStar_Pervasives_Native.None)
                          in
                       (match uu____74256 with
                        | FStar_Pervasives_Native.Some uu____74274 ->
                            (g1, [])
                        | uu____74277 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____74287 = FStar_Extraction_ML_Term.term_as_mlexpr g e  in
           (match uu____74287 with
            | (ml_main,uu____74301,uu____74302) ->
                let uu____74303 =
                  let uu____74306 =
                    let uu____74307 =
                      FStar_Extraction_ML_Util.mlloc_of_range
                        se.FStar_Syntax_Syntax.sigrng
                       in
                    FStar_Extraction_ML_Syntax.MLM_Loc uu____74307  in
                  [uu____74306; FStar_Extraction_ML_Syntax.MLM_Top ml_main]
                   in
                (g, uu____74303))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____74310 ->
           failwith "impossible -- removed by tc.fs"
       | FStar_Syntax_Syntax.Sig_assume uu____74318 -> (g, [])
       | FStar_Syntax_Syntax.Sig_sub_effect uu____74327 -> (g, [])
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____74330 -> (g, [])
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
      let uu____74372 = FStar_Options.restore_cmd_line_options true  in
      let name =
        FStar_Extraction_ML_Syntax.mlpath_of_lident
          m.FStar_Syntax_Syntax.name
         in
      let g1 =
        let uu___1527_74376 = g  in
        let uu____74377 =
          FStar_TypeChecker_Env.set_current_module
            g.FStar_Extraction_ML_UEnv.env_tcenv m.FStar_Syntax_Syntax.name
           in
        {
          FStar_Extraction_ML_UEnv.env_tcenv = uu____74377;
          FStar_Extraction_ML_UEnv.env_bindings =
            (uu___1527_74376.FStar_Extraction_ML_UEnv.env_bindings);
          FStar_Extraction_ML_UEnv.tydefs =
            (uu___1527_74376.FStar_Extraction_ML_UEnv.tydefs);
          FStar_Extraction_ML_UEnv.type_names =
            (uu___1527_74376.FStar_Extraction_ML_UEnv.type_names);
          FStar_Extraction_ML_UEnv.currentModule = name
        }  in
      let uu____74378 =
        FStar_Util.fold_map
          (fun g2  ->
             fun se  ->
               let uu____74397 =
                 FStar_Options.debug_module
                   (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                  in
               if uu____74397
               then
                 let nm =
                   let uu____74408 =
                     FStar_All.pipe_right
                       (FStar_Syntax_Util.lids_of_sigelt se)
                       (FStar_List.map FStar_Ident.string_of_lid)
                      in
                   FStar_All.pipe_right uu____74408
                     (FStar_String.concat ", ")
                    in
                 (FStar_Util.print1 "+++About to extract {%s}\n" nm;
                  (let uu____74425 =
                     FStar_Util.format1 "---Extracted {%s}" nm  in
                   FStar_Util.measure_execution_time uu____74425
                     (fun uu____74435  -> extract_sig g2 se)))
               else extract_sig g2 se) g1 m.FStar_Syntax_Syntax.declarations
         in
      match uu____74378 with
      | (g2,sigs) ->
          let mlm = FStar_List.flatten sigs  in
          let is_kremlin =
            let uu____74457 = FStar_Options.codegen ()  in
            uu____74457 =
              (FStar_Pervasives_Native.Some FStar_Options.Kremlin)
             in
          if
            ((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims") &&
              (is_kremlin ||
                 (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface))
          then
            ((let uu____74472 =
                let uu____74474 = FStar_Options.silent ()  in
                Prims.op_Negation uu____74474  in
              if uu____74472
              then
                let uu____74477 =
                  FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
                FStar_Util.print1 "Extracted module %s\n" uu____74477
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
      (let uu____74552 = FStar_Options.restore_cmd_line_options true  in
       FStar_All.pipe_left (fun a2  -> ()) uu____74552);
      (let uu____74555 =
         let uu____74557 =
           FStar_Options.should_extract
             (m.FStar_Syntax_Syntax.name).FStar_Ident.str
            in
         Prims.op_Negation uu____74557  in
       if uu____74555
       then
         let uu____74560 =
           let uu____74562 =
             FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
           FStar_Util.format1
             "Extract called on a module %s that should not be extracted"
             uu____74562
            in
         failwith uu____74560
       else ());
      (let uu____74567 = FStar_Options.interactive ()  in
       if uu____74567
       then (g, FStar_Pervasives_Native.None)
       else
         (let res =
            let uu____74587 = FStar_Options.debug_any ()  in
            if uu____74587
            then
              let msg =
                let uu____74598 =
                  FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name
                   in
                FStar_Util.format1 "Extracting module %s\n" uu____74598  in
              FStar_Util.measure_execution_time msg
                (fun uu____74608  -> extract' g m)
            else extract' g m  in
          (let uu____74612 = FStar_Options.restore_cmd_line_options true  in
           FStar_All.pipe_left (fun a3  -> ()) uu____74612);
          res))
  
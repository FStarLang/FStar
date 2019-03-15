open Prims
type env_t = FStar_Extraction_ML_UEnv.uenv
let (fail_exp :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun lid  ->
    fun t  ->
      let uu____63767 =
        let uu____63774 =
          let uu____63775 =
            let uu____63792 =
              FStar_Syntax_Syntax.fvar FStar_Parser_Const.failwith_lid
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            let uu____63795 =
              let uu____63806 = FStar_Syntax_Syntax.iarg t  in
              let uu____63815 =
                let uu____63826 =
                  let uu____63835 =
                    let uu____63836 =
                      let uu____63843 =
                        let uu____63844 =
                          let uu____63845 =
                            let uu____63851 =
                              let uu____63853 =
                                FStar_Syntax_Print.lid_to_string lid  in
                              Prims.op_Hat "Not yet implemented:" uu____63853
                               in
                            (uu____63851, FStar_Range.dummyRange)  in
                          FStar_Const.Const_string uu____63845  in
                        FStar_Syntax_Syntax.Tm_constant uu____63844  in
                      FStar_Syntax_Syntax.mk uu____63843  in
                    uu____63836 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange
                     in
                  FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____63835
                   in
                [uu____63826]  in
              uu____63806 :: uu____63815  in
            (uu____63792, uu____63795)  in
          FStar_Syntax_Syntax.Tm_app uu____63775  in
        FStar_Syntax_Syntax.mk uu____63774  in
      uu____63767 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (always_fail :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.letbinding)
  =
  fun lid  ->
    fun t  ->
      let imp =
        let uu____63919 = FStar_Syntax_Util.arrow_formals t  in
        match uu____63919 with
        | ([],t1) ->
            let b =
              let uu____63962 =
                FStar_Syntax_Syntax.gen_bv "_" FStar_Pervasives_Native.None
                  t1
                 in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____63962
               in
            let uu____63970 = fail_exp lid t1  in
            FStar_Syntax_Util.abs [b] uu____63970
              FStar_Pervasives_Native.None
        | (bs,t1) ->
            let uu____64007 = fail_exp lid t1  in
            FStar_Syntax_Util.abs bs uu____64007 FStar_Pervasives_Native.None
         in
      let lb =
        let uu____64011 =
          let uu____64016 =
            FStar_Syntax_Syntax.lid_as_fv lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Util.Inr uu____64016  in
        {
          FStar_Syntax_Syntax.lbname = uu____64011;
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
  'Auu____64038 . 'Auu____64038 Prims.list -> ('Auu____64038 * 'Auu____64038)
  =
  fun uu___612_64049  ->
    match uu___612_64049 with
    | a::b::[] -> (a, b)
    | uu____64054 -> failwith "Expected a list with 2 elements"
  
let (flag_of_qual :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option)
  =
  fun uu___613_64069  ->
    match uu___613_64069 with
    | FStar_Syntax_Syntax.Assumption  ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Assumed
    | FStar_Syntax_Syntax.Private  ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Private
    | FStar_Syntax_Syntax.NoExtract  ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.NoExtract
    | uu____64072 -> FStar_Pervasives_Native.None
  
let rec (extract_meta :
  FStar_Syntax_Syntax.term ->
    FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option)
  =
  fun x  ->
    let uu____64081 = FStar_Syntax_Subst.compress x  in
    match uu____64081 with
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
        FStar_Syntax_Syntax.pos = uu____64085;
        FStar_Syntax_Syntax.vars = uu____64086;_} ->
        let uu____64089 =
          let uu____64091 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____64091  in
        (match uu____64089 with
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
         | uu____64101 -> FStar_Pervasives_Native.None)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____64104;
             FStar_Syntax_Syntax.vars = uu____64105;_},({
                                                          FStar_Syntax_Syntax.n
                                                            =
                                                            FStar_Syntax_Syntax.Tm_constant
                                                            (FStar_Const.Const_string
                                                            (s,uu____64107));
                                                          FStar_Syntax_Syntax.pos
                                                            = uu____64108;
                                                          FStar_Syntax_Syntax.vars
                                                            = uu____64109;_},uu____64110)::[]);
        FStar_Syntax_Syntax.pos = uu____64111;
        FStar_Syntax_Syntax.vars = uu____64112;_} ->
        let uu____64155 =
          let uu____64157 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____64157  in
        (match uu____64155 with
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
         | uu____64166 -> FStar_Pervasives_Native.None)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("KremlinPrivate",uu____64168));
        FStar_Syntax_Syntax.pos = uu____64169;
        FStar_Syntax_Syntax.vars = uu____64170;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Private
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("c_inline",uu____64175));
        FStar_Syntax_Syntax.pos = uu____64176;
        FStar_Syntax_Syntax.vars = uu____64177;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.CInline
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("substitute",uu____64182));
        FStar_Syntax_Syntax.pos = uu____64183;
        FStar_Syntax_Syntax.vars = uu____64184;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Substitute
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_meta (x1,uu____64190);
        FStar_Syntax_Syntax.pos = uu____64191;
        FStar_Syntax_Syntax.vars = uu____64192;_} -> extract_meta x1
    | uu____64199 -> FStar_Pervasives_Native.None
  
let (extract_metadata :
  FStar_Syntax_Syntax.term Prims.list ->
    FStar_Extraction_ML_Syntax.meta Prims.list)
  = fun metas  -> FStar_List.choose extract_meta metas 
let binders_as_mlty_binders :
  'Auu____64219 .
    FStar_Extraction_ML_UEnv.uenv ->
      (FStar_Syntax_Syntax.bv * 'Auu____64219) Prims.list ->
        (FStar_Extraction_ML_UEnv.uenv * Prims.string Prims.list)
  =
  fun env  ->
    fun bs  ->
      FStar_Util.fold_map
        (fun env1  ->
           fun uu____64261  ->
             match uu____64261 with
             | (bv,uu____64272) ->
                 let uu____64273 =
                   let uu____64274 =
                     let uu____64277 =
                       let uu____64278 =
                         FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv  in
                       FStar_Extraction_ML_Syntax.MLTY_Var uu____64278  in
                     FStar_Pervasives_Native.Some uu____64277  in
                   FStar_Extraction_ML_UEnv.extend_ty env1 bv uu____64274  in
                 let uu____64280 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv
                    in
                 (uu____64273, uu____64280)) env bs
  
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
    let uu____64481 = FStar_Syntax_Print.lid_to_string i.iname  in
    let uu____64483 = FStar_Syntax_Print.binders_to_string " " i.iparams  in
    let uu____64486 = FStar_Syntax_Print.term_to_string i.ityp  in
    let uu____64488 =
      let uu____64490 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d  ->
                let uu____64504 = FStar_Syntax_Print.lid_to_string d.dname
                   in
                let uu____64506 =
                  let uu____64508 = FStar_Syntax_Print.term_to_string d.dtyp
                     in
                  Prims.op_Hat " : " uu____64508  in
                Prims.op_Hat uu____64504 uu____64506))
         in
      FStar_All.pipe_right uu____64490 (FStar_String.concat "\n\t\t")  in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____64481 uu____64483
      uu____64486 uu____64488
  
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
          let uu____64562 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun se  ->
                   match se.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,_us,bs,t,_mut_i,datas) ->
                       let uu____64610 = FStar_Syntax_Subst.open_term bs t
                          in
                       (match uu____64610 with
                        | (bs1,t1) ->
                            let datas1 =
                              FStar_All.pipe_right ses
                                (FStar_List.collect
                                   (fun se1  ->
                                      match se1.FStar_Syntax_Syntax.sigel
                                      with
                                      | FStar_Syntax_Syntax.Sig_datacon
                                          (d,uu____64649,t2,l',nparams,uu____64653)
                                          when FStar_Ident.lid_equals l l' ->
                                          let uu____64660 =
                                            FStar_Syntax_Util.arrow_formals
                                              t2
                                             in
                                          (match uu____64660 with
                                           | (bs',body) ->
                                               let uu____64699 =
                                                 FStar_Util.first_N
                                                   (FStar_List.length bs1)
                                                   bs'
                                                  in
                                               (match uu____64699 with
                                                | (bs_params,rest) ->
                                                    let subst1 =
                                                      FStar_List.map2
                                                        (fun uu____64790  ->
                                                           fun uu____64791 
                                                             ->
                                                             match (uu____64790,
                                                                    uu____64791)
                                                             with
                                                             | ((b',uu____64817),
                                                                (b,uu____64819))
                                                                 ->
                                                                 let uu____64840
                                                                   =
                                                                   let uu____64847
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    b  in
                                                                   (b',
                                                                    uu____64847)
                                                                    in
                                                                 FStar_Syntax_Syntax.NT
                                                                   uu____64840)
                                                        bs_params bs1
                                                       in
                                                    let t3 =
                                                      let uu____64853 =
                                                        let uu____64854 =
                                                          FStar_Syntax_Syntax.mk_Total
                                                            body
                                                           in
                                                        FStar_Syntax_Util.arrow
                                                          rest uu____64854
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____64853
                                                        (FStar_Syntax_Subst.subst
                                                           subst1)
                                                       in
                                                    [{ dname = d; dtyp = t3 }]))
                                      | uu____64857 -> []))
                               in
                            let metadata =
                              let uu____64861 =
                                extract_metadata
                                  (FStar_List.append
                                     se.FStar_Syntax_Syntax.sigattrs attrs)
                                 in
                              let uu____64864 =
                                FStar_List.choose flag_of_qual quals  in
                              FStar_List.append uu____64861 uu____64864  in
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
                   | uu____64871 -> (env1, [])) env ses
             in
          match uu____64562 with
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
    let uu___820_65051 = empty_iface  in
    {
      iface_module_name = (uu___820_65051.iface_module_name);
      iface_bindings = fvs;
      iface_tydefs = (uu___820_65051.iface_tydefs);
      iface_type_names = (uu___820_65051.iface_type_names)
    }
  
let (iface_of_tydefs : FStar_Extraction_ML_UEnv.tydef Prims.list -> iface) =
  fun tds  ->
    let uu___823_65062 = empty_iface  in
    let uu____65063 =
      FStar_List.map (fun td  -> td.FStar_Extraction_ML_UEnv.tydef_fv) tds
       in
    {
      iface_module_name = (uu___823_65062.iface_module_name);
      iface_bindings = (uu___823_65062.iface_bindings);
      iface_tydefs = tds;
      iface_type_names = uu____65063
    }
  
let (iface_of_type_names : FStar_Syntax_Syntax.fv Prims.list -> iface) =
  fun fvs  ->
    let uu___827_65078 = empty_iface  in
    {
      iface_module_name = (uu___827_65078.iface_module_name);
      iface_bindings = (uu___827_65078.iface_bindings);
      iface_tydefs = (uu___827_65078.iface_tydefs);
      iface_type_names = fvs
    }
  
let (iface_union : iface -> iface -> iface) =
  fun if1  ->
    fun if2  ->
      let uu____65090 =
        if if1.iface_module_name <> if1.iface_module_name
        then failwith "Union not defined"
        else if1.iface_module_name  in
      {
        iface_module_name = uu____65090;
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
  'Auu____65135 .
    FStar_Extraction_ML_Syntax.mlpath ->
      ('Auu____65135 * FStar_Extraction_ML_Syntax.mlty) -> Prims.string
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
      let uu____65167 =
        FStar_Extraction_ML_Code.string_of_mlexpr cm
          e.FStar_Extraction_ML_UEnv.exp_b_expr
         in
      let uu____65169 =
        tscheme_to_string cm e.FStar_Extraction_ML_UEnv.exp_b_tscheme  in
      let uu____65171 =
        FStar_Util.string_of_bool e.FStar_Extraction_ML_UEnv.exp_b_inst_ok
         in
      FStar_Util.format4
        "{\n\texp_b_name = %s\n\texp_b_expr = %s\n\texp_b_tscheme = %s\n\texp_b_is_rec = %s }"
        e.FStar_Extraction_ML_UEnv.exp_b_name uu____65167 uu____65169
        uu____65171
  
let (print_binding :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_UEnv.exp_binding) ->
      Prims.string)
  =
  fun cm  ->
    fun uu____65189  ->
      match uu____65189 with
      | (fv,exp_binding) ->
          let uu____65197 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____65199 = print_exp_binding cm exp_binding  in
          FStar_Util.format2 "(%s, %s)" uu____65197 uu____65199
  
let (print_tydef :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_UEnv.tydef -> Prims.string)
  =
  fun cm  ->
    fun tydef  ->
      let uu____65214 =
        FStar_Syntax_Print.fv_to_string
          tydef.FStar_Extraction_ML_UEnv.tydef_fv
         in
      let uu____65216 =
        tscheme_to_string cm tydef.FStar_Extraction_ML_UEnv.tydef_def  in
      FStar_Util.format2 "(%s, %s)" uu____65214 uu____65216
  
let (iface_to_string : iface -> Prims.string) =
  fun iface1  ->
    let cm = iface1.iface_module_name  in
    let print_type_name tn = FStar_Syntax_Print.fv_to_string tn  in
    let uu____65234 =
      let uu____65236 =
        FStar_List.map (print_binding cm) iface1.iface_bindings  in
      FStar_All.pipe_right uu____65236 (FStar_String.concat "\n")  in
    let uu____65250 =
      let uu____65252 = FStar_List.map (print_tydef cm) iface1.iface_tydefs
         in
      FStar_All.pipe_right uu____65252 (FStar_String.concat "\n")  in
    let uu____65262 =
      let uu____65264 =
        FStar_List.map print_type_name iface1.iface_type_names  in
      FStar_All.pipe_right uu____65264 (FStar_String.concat "\n")  in
    FStar_Util.format4
      "Interface %s = {\niface_bindings=\n%s;\n\niface_tydefs=\n%s;\n\niface_type_names=%s;\n}"
      (mlpath_to_string iface1.iface_module_name) uu____65234 uu____65250
      uu____65262
  
let (gamma_to_string : FStar_Extraction_ML_UEnv.uenv -> Prims.string) =
  fun env  ->
    let cm = env.FStar_Extraction_ML_UEnv.currentModule  in
    let gamma =
      FStar_List.collect
        (fun uu___614_65297  ->
           match uu___614_65297 with
           | FStar_Extraction_ML_UEnv.Fv (b,e) -> [(b, e)]
           | uu____65314 -> []) env.FStar_Extraction_ML_UEnv.env_bindings
       in
    let uu____65319 =
      let uu____65321 = FStar_List.map (print_binding cm) gamma  in
      FStar_All.pipe_right uu____65321 (FStar_String.concat "\n")  in
    FStar_Util.format1 "Gamma = {\n %s }" uu____65319
  
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
          let uu____65381 =
            let uu____65390 =
              FStar_TypeChecker_Env.open_universes_in
                env.FStar_Extraction_ML_UEnv.env_tcenv
                lb.FStar_Syntax_Syntax.lbunivs
                [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp]
               in
            match uu____65390 with
            | (tcenv,uu____65408,def_typ) ->
                let uu____65414 = as_pair def_typ  in (tcenv, uu____65414)
             in
          match uu____65381 with
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
                let uu____65445 =
                  let uu____65446 = FStar_Syntax_Subst.compress lbdef1  in
                  FStar_All.pipe_right uu____65446 FStar_Syntax_Util.unmeta
                   in
                FStar_All.pipe_right uu____65445 FStar_Syntax_Util.un_uinst
                 in
              let def1 =
                match def.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_abs uu____65454 ->
                    FStar_Extraction_ML_Term.normalize_abs def
                | uu____65473 -> def  in
              let uu____65474 =
                match def1.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____65485) ->
                    FStar_Syntax_Subst.open_term bs body
                | uu____65510 -> ([], def1)  in
              (match uu____65474 with
               | (bs,body) ->
                   let assumed =
                     FStar_Util.for_some
                       (fun uu___615_65530  ->
                          match uu___615_65530 with
                          | FStar_Syntax_Syntax.Assumption  -> true
                          | uu____65533 -> false) quals
                      in
                   let uu____65535 = binders_as_mlty_binders env bs  in
                   (match uu____65535 with
                    | (env1,ml_bs) ->
                        let body1 =
                          let uu____65562 =
                            FStar_Extraction_ML_Term.term_as_mlty env1 body
                             in
                          FStar_All.pipe_right uu____65562
                            (FStar_Extraction_ML_Util.eraseTypeDeep
                               (FStar_Extraction_ML_Util.udelta_unfold env1))
                           in
                        let mangled_projector =
                          let uu____65567 =
                            FStar_All.pipe_right quals
                              (FStar_Util.for_some
                                 (fun uu___616_65574  ->
                                    match uu___616_65574 with
                                    | FStar_Syntax_Syntax.Projector
                                        uu____65576 -> true
                                    | uu____65582 -> false))
                             in
                          if uu____65567
                          then
                            let mname = mangle_projector_lid lid  in
                            FStar_Pervasives_Native.Some
                              ((mname.FStar_Ident.ident).FStar_Ident.idText)
                          else FStar_Pervasives_Native.None  in
                        let metadata =
                          let uu____65596 = extract_metadata attrs  in
                          let uu____65599 =
                            FStar_List.choose flag_of_qual quals  in
                          FStar_List.append uu____65596 uu____65599  in
                        let td =
                          let uu____65622 = lident_as_mlsymbol lid  in
                          (assumed, uu____65622, mangled_projector, ml_bs,
                            metadata,
                            (FStar_Pervasives_Native.Some
                               (FStar_Extraction_ML_Syntax.MLTD_Abbrev body1)))
                           in
                        let def2 =
                          let uu____65634 =
                            let uu____65635 =
                              let uu____65636 = FStar_Ident.range_of_lid lid
                                 in
                              FStar_Extraction_ML_Util.mlloc_of_range
                                uu____65636
                               in
                            FStar_Extraction_ML_Syntax.MLM_Loc uu____65635
                             in
                          [uu____65634;
                          FStar_Extraction_ML_Syntax.MLM_Ty [td]]  in
                        let uu____65637 =
                          let uu____65642 =
                            FStar_All.pipe_right quals
                              (FStar_Util.for_some
                                 (fun uu___617_65648  ->
                                    match uu___617_65648 with
                                    | FStar_Syntax_Syntax.Assumption  -> true
                                    | FStar_Syntax_Syntax.New  -> true
                                    | uu____65652 -> false))
                             in
                          if uu____65642
                          then
                            let uu____65659 =
                              FStar_Extraction_ML_UEnv.extend_type_name env
                                fv
                               in
                            (uu____65659, (iface_of_type_names [fv]))
                          else
                            (let uu____65662 =
                               FStar_Extraction_ML_UEnv.extend_tydef env fv
                                 td
                                in
                             match uu____65662 with
                             | (env2,tydef) ->
                                 let uu____65673 = iface_of_tydefs [tydef]
                                    in
                                 (env2, uu____65673))
                           in
                        (match uu____65637 with
                         | (env2,iface1) -> (env2, iface1, def2))))
  
let (extract_bundle_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt -> (env_t * iface))
  =
  fun env  ->
    fun se  ->
      let extract_ctor env_iparams ml_tyvars env1 ctor =
        let mlt =
          let uu____65749 =
            FStar_Extraction_ML_Term.term_as_mlty env_iparams ctor.dtyp  in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env_iparams) uu____65749
           in
        let tys = (ml_tyvars, mlt)  in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp  in
        let uu____65756 =
          FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false  in
        match uu____65756 with | (env2,uu____65775,b) -> (env2, (fvv, b))  in
      let extract_one_family env1 ind =
        let uu____65814 = binders_as_mlty_binders env1 ind.iparams  in
        match uu____65814 with
        | (env_iparams,vars) ->
            let uu____65842 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor env_iparams vars) env1)
               in
            (match uu____65842 with | (env2,ctors) -> (env2, ctors))
         in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____65906,t,uu____65908,uu____65909,uu____65910);
            FStar_Syntax_Syntax.sigrng = uu____65911;
            FStar_Syntax_Syntax.sigquals = uu____65912;
            FStar_Syntax_Syntax.sigmeta = uu____65913;
            FStar_Syntax_Syntax.sigattrs = uu____65914;_}::[],uu____65915),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____65934 = extract_ctor env [] env { dname = l; dtyp = t }
             in
          (match uu____65934 with
           | (env1,ctor) -> (env1, (iface_of_bindings [ctor])))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____65967),quals) ->
          let uu____65981 =
            bundle_as_inductive_families env ses quals
              se.FStar_Syntax_Syntax.sigattrs
             in
          (match uu____65981 with
           | (env1,ifams) ->
               let uu____65998 =
                 FStar_Util.fold_map extract_one_family env1 ifams  in
               (match uu____65998 with
                | (env2,td) ->
                    let uu____66039 =
                      let uu____66040 =
                        let uu____66041 =
                          FStar_List.map (fun x  -> x.ifv) ifams  in
                        iface_of_type_names uu____66041  in
                      iface_union uu____66040
                        (iface_of_bindings (FStar_List.flatten td))
                       in
                    (env2, uu____66039)))
      | uu____66050 -> failwith "Unexpected signature element"
  
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
              let uu____66125 =
                let uu____66127 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun uu___618_66133  ->
                          match uu___618_66133 with
                          | FStar_Syntax_Syntax.Assumption  -> true
                          | uu____66136 -> false))
                   in
                Prims.op_Negation uu____66127  in
              if uu____66125
              then (g, empty_iface, [])
              else
                (let uu____66151 = FStar_Syntax_Util.arrow_formals t  in
                 match uu____66151 with
                 | (bs,uu____66175) ->
                     let fv =
                       FStar_Syntax_Syntax.lid_as_fv lid
                         FStar_Syntax_Syntax.delta_constant
                         FStar_Pervasives_Native.None
                        in
                     let lb =
                       let uu____66198 =
                         FStar_Syntax_Util.abs bs FStar_Syntax_Syntax.t_unit
                           FStar_Pervasives_Native.None
                          in
                       {
                         FStar_Syntax_Syntax.lbname = (FStar_Util.Inr fv);
                         FStar_Syntax_Syntax.lbunivs = univs1;
                         FStar_Syntax_Syntax.lbtyp = t;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_Tot_lid;
                         FStar_Syntax_Syntax.lbdef = uu____66198;
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
        let uu____66261 =
          FStar_Extraction_ML_UEnv.extend_fv' g1 fv ml_name tysc false false
           in
        match uu____66261 with
        | (g2,mangled_name,exp_binding) ->
            ((let uu____66283 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g2.FStar_Extraction_ML_UEnv.env_tcenv)
                  (FStar_Options.Other "ExtractionReify")
                 in
              if uu____66283
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
        (let uu____66319 =
           FStar_All.pipe_left
             (FStar_TypeChecker_Env.debug
                g.FStar_Extraction_ML_UEnv.env_tcenv)
             (FStar_Options.Other "ExtractionReify")
            in
         if uu____66319
         then
           let uu____66324 = FStar_Syntax_Print.term_to_string tm  in
           FStar_Util.print1 "extract_fv term: %s\n" uu____66324
         else ());
        (let uu____66329 =
           let uu____66330 = FStar_Syntax_Subst.compress tm  in
           uu____66330.FStar_Syntax_Syntax.n  in
         match uu____66329 with
         | FStar_Syntax_Syntax.Tm_uinst (tm1,uu____66338) -> extract_fv tm1
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             let mlp =
               FStar_Extraction_ML_Syntax.mlpath_of_lident
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             let uu____66345 = FStar_Extraction_ML_UEnv.lookup_fv g fv  in
             (match uu____66345 with
              | { FStar_Extraction_ML_UEnv.exp_b_name = uu____66350;
                  FStar_Extraction_ML_UEnv.exp_b_expr = uu____66351;
                  FStar_Extraction_ML_UEnv.exp_b_tscheme = tysc;
                  FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____66353;_} ->
                  let uu____66356 =
                    FStar_All.pipe_left
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.MLTY_Top)
                      (FStar_Extraction_ML_Syntax.MLE_Name mlp)
                     in
                  (uu____66356, tysc))
         | uu____66357 ->
             let uu____66358 =
               let uu____66360 =
                 FStar_Range.string_of_range tm.FStar_Syntax_Syntax.pos  in
               let uu____66362 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.format2 "(%s) Not an fv: %s" uu____66360
                 uu____66362
                in
             failwith uu____66358)
         in
      let extract_action g1 a =
        (let uu____66390 =
           FStar_All.pipe_left
             (FStar_TypeChecker_Env.debug
                g1.FStar_Extraction_ML_UEnv.env_tcenv)
             (FStar_Options.Other "ExtractionReify")
            in
         if uu____66390
         then
           let uu____66395 =
             FStar_Syntax_Print.term_to_string
               a.FStar_Syntax_Syntax.action_typ
              in
           let uu____66397 =
             FStar_Syntax_Print.term_to_string
               a.FStar_Syntax_Syntax.action_defn
              in
           FStar_Util.print2 "Action type %s and term %s\n" uu____66395
             uu____66397
         else ());
        (let uu____66402 = FStar_Extraction_ML_UEnv.action_name ed a  in
         match uu____66402 with
         | (a_nm,a_lid) ->
             let lbname =
               let uu____66422 =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some
                      ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                   FStar_Syntax_Syntax.tun
                  in
               FStar_Util.Inl uu____66422  in
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
             let uu____66452 =
               FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb  in
             (match uu____66452 with
              | (a_let,uu____66468,ty) ->
                  ((let uu____66471 =
                      FStar_All.pipe_left
                        (FStar_TypeChecker_Env.debug
                           g1.FStar_Extraction_ML_UEnv.env_tcenv)
                        (FStar_Options.Other "ExtractionReify")
                       in
                    if uu____66471
                    then
                      let uu____66476 =
                        FStar_Extraction_ML_Code.string_of_mlexpr a_nm a_let
                         in
                      FStar_Util.print1 "Extracted action term: %s\n"
                        uu____66476
                    else ());
                   (let uu____66481 =
                      match a_let.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Let
                          ((uu____66504,mllb::[]),uu____66506) ->
                          (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc
                           with
                           | FStar_Pervasives_Native.Some tysc ->
                               ((mllb.FStar_Extraction_ML_Syntax.mllb_def),
                                 tysc)
                           | FStar_Pervasives_Native.None  ->
                               failwith "No type scheme")
                      | uu____66546 -> failwith "Impossible"  in
                    match uu____66481 with
                    | (exp,tysc) ->
                        ((let uu____66584 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug
                                 g1.FStar_Extraction_ML_UEnv.env_tcenv)
                              (FStar_Options.Other "ExtractionReify")
                             in
                          if uu____66584
                          then
                            ((let uu____66590 =
                                FStar_Extraction_ML_Code.string_of_mlty a_nm
                                  (FStar_Pervasives_Native.snd tysc)
                                 in
                              FStar_Util.print1 "Extracted action type: %s\n"
                                uu____66590);
                             FStar_List.iter
                               (fun x  ->
                                  FStar_Util.print1 "and binders: %s\n" x)
                               (FStar_Pervasives_Native.fst tysc))
                          else ());
                         (let uu____66606 = extend_env g1 a_lid a_nm exp tysc
                             in
                          match uu____66606 with
                          | (env,iface1,impl) -> (env, (iface1, impl))))))))
         in
      let uu____66628 =
        let uu____66635 =
          extract_fv
            (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.return_repr)
           in
        match uu____66635 with
        | (return_tm,ty_sc) ->
            let uu____66652 =
              FStar_Extraction_ML_UEnv.monad_op_name ed "return"  in
            (match uu____66652 with
             | (return_nm,return_lid) ->
                 extend_env g return_lid return_nm return_tm ty_sc)
         in
      match uu____66628 with
      | (g1,return_iface,return_decl) ->
          let uu____66677 =
            let uu____66684 =
              extract_fv
                (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.bind_repr)
               in
            match uu____66684 with
            | (bind_tm,ty_sc) ->
                let uu____66701 =
                  FStar_Extraction_ML_UEnv.monad_op_name ed "bind"  in
                (match uu____66701 with
                 | (bind_nm,bind_lid) ->
                     extend_env g1 bind_lid bind_nm bind_tm ty_sc)
             in
          (match uu____66677 with
           | (g2,bind_iface,bind_decl) ->
               let uu____66726 =
                 FStar_Util.fold_map extract_action g2
                   ed.FStar_Syntax_Syntax.actions
                  in
               (match uu____66726 with
                | (g3,actions) ->
                    let uu____66763 = FStar_List.unzip actions  in
                    (match uu____66763 with
                     | (actions_iface,actions1) ->
                         let uu____66790 =
                           iface_union_l (return_iface :: bind_iface ::
                             actions_iface)
                            in
                         (g3, uu____66790, (return_decl :: bind_decl ::
                           actions1)))))
  
let (extract_sigelt_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle uu____66812 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____66821 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_datacon uu____66838 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) when
          FStar_Extraction_ML_Term.is_arity g t ->
          let uu____66857 =
            extract_type_declaration g lid se.FStar_Syntax_Syntax.sigquals
              se.FStar_Syntax_Syntax.sigattrs univs1 t
             in
          (match uu____66857 with | (env,iface1,uu____66872) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____66878) when
          FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp ->
          let uu____66887 =
            extract_typ_abbrev g se.FStar_Syntax_Syntax.sigquals
              se.FStar_Syntax_Syntax.sigattrs lb
             in
          (match uu____66887 with | (env,iface1,uu____66902) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,_univs,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let uu____66913 =
            (FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption))
              &&
              (let uu____66919 =
                 FStar_TypeChecker_Util.must_erase_for_extraction
                   g.FStar_Extraction_ML_UEnv.env_tcenv t
                  in
               Prims.op_Negation uu____66919)
             in
          if uu____66913
          then
            let uu____66926 =
              let uu____66937 =
                let uu____66938 =
                  let uu____66941 = always_fail lid t  in [uu____66941]  in
                (false, uu____66938)  in
              FStar_Extraction_ML_Term.extract_lb_iface g uu____66937  in
            (match uu____66926 with
             | (g1,bindings) -> (g1, (iface_of_bindings bindings)))
          else (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____66967) ->
          let uu____66972 = FStar_Extraction_ML_Term.extract_lb_iface g lbs
             in
          (match uu____66972 with
           | (g1,bindings) -> (g1, (iface_of_bindings bindings)))
      | FStar_Syntax_Syntax.Sig_main uu____67001 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____67002 ->
          (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_assume uu____67003 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____67010 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____67011 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          (FStar_Syntax_Util.process_pragma p se.FStar_Syntax_Syntax.sigrng;
           (g, empty_iface))
      | FStar_Syntax_Syntax.Sig_splice uu____67026 ->
          failwith "impossible: trying to extract splice"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____67039 =
            (FStar_TypeChecker_Env.is_reifiable_effect
               g.FStar_Extraction_ML_UEnv.env_tcenv
               ed.FStar_Syntax_Syntax.mname)
              && (FStar_List.isEmpty ed.FStar_Syntax_Syntax.binders)
             in
          if uu____67039
          then
            let uu____67052 = extract_reifiable_effect g ed  in
            (match uu____67052 with
             | (env,iface1,uu____67067) -> (env, iface1))
          else (g, empty_iface)
  
let (extract_iface' :
  env_t ->
    FStar_Syntax_Syntax.modul -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun modul  ->
      let uu____67089 = FStar_Options.interactive ()  in
      if uu____67089
      then (g, empty_iface)
      else
        (let uu____67098 = FStar_Options.restore_cmd_line_options true  in
         let decls = modul.FStar_Syntax_Syntax.declarations  in
         let iface1 =
           let uu___1166_67102 = empty_iface  in
           {
             iface_module_name = (g.FStar_Extraction_ML_UEnv.currentModule);
             iface_bindings = (uu___1166_67102.iface_bindings);
             iface_tydefs = (uu___1166_67102.iface_tydefs);
             iface_type_names = (uu___1166_67102.iface_type_names)
           }  in
         let res =
           FStar_List.fold_left
             (fun uu____67120  ->
                fun se  ->
                  match uu____67120 with
                  | (g1,iface2) ->
                      let uu____67132 = extract_sigelt_iface g1 se  in
                      (match uu____67132 with
                       | (g2,iface') ->
                           let uu____67143 = iface_union iface2 iface'  in
                           (g2, uu____67143))) (g, iface1) decls
            in
         (let uu____67145 = FStar_Options.restore_cmd_line_options true  in
          FStar_All.pipe_left (fun a1  -> ()) uu____67145);
         res)
  
let (extract_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.modul -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun modul  ->
      let uu____67162 = FStar_Options.debug_any ()  in
      if uu____67162
      then
        let uu____67169 =
          FStar_Util.format1 "Extracted interface of %s"
            (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
           in
        FStar_Util.measure_execution_time uu____67169
          (fun uu____67177  -> extract_iface' g modul)
      else extract_iface' g modul
  
let (extend_with_iface :
  FStar_Extraction_ML_UEnv.uenv -> iface -> FStar_Extraction_ML_UEnv.uenv) =
  fun g  ->
    fun iface1  ->
      let uu___1184_67191 = g  in
      let uu____67192 =
        let uu____67195 =
          FStar_List.map (fun _67202  -> FStar_Extraction_ML_UEnv.Fv _67202)
            iface1.iface_bindings
           in
        FStar_List.append uu____67195 g.FStar_Extraction_ML_UEnv.env_bindings
         in
      {
        FStar_Extraction_ML_UEnv.env_tcenv =
          (uu___1184_67191.FStar_Extraction_ML_UEnv.env_tcenv);
        FStar_Extraction_ML_UEnv.env_bindings = uu____67192;
        FStar_Extraction_ML_UEnv.tydefs =
          (FStar_List.append iface1.iface_tydefs
             g.FStar_Extraction_ML_UEnv.tydefs);
        FStar_Extraction_ML_UEnv.type_names =
          (FStar_List.append iface1.iface_type_names
             g.FStar_Extraction_ML_UEnv.type_names);
        FStar_Extraction_ML_UEnv.currentModule =
          (uu___1184_67191.FStar_Extraction_ML_UEnv.currentModule)
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
          let uu____67280 =
            FStar_Extraction_ML_Term.term_as_mlty env_iparams ctor.dtyp  in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env_iparams) uu____67280
           in
        let steps =
          [FStar_TypeChecker_Env.Inlining;
          FStar_TypeChecker_Env.UnfoldUntil
            FStar_Syntax_Syntax.delta_constant;
          FStar_TypeChecker_Env.EraseUniverses;
          FStar_TypeChecker_Env.AllowUnboundUniverses]  in
        let names1 =
          let uu____67288 =
            let uu____67289 =
              let uu____67292 =
                FStar_TypeChecker_Normalize.normalize steps
                  env_iparams.FStar_Extraction_ML_UEnv.env_tcenv ctor.dtyp
                 in
              FStar_Syntax_Subst.compress uu____67292  in
            uu____67289.FStar_Syntax_Syntax.n  in
          match uu____67288 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,uu____67297) ->
              FStar_List.map
                (fun uu____67330  ->
                   match uu____67330 with
                   | ({ FStar_Syntax_Syntax.ppname = ppname;
                        FStar_Syntax_Syntax.index = uu____67339;
                        FStar_Syntax_Syntax.sort = uu____67340;_},uu____67341)
                       -> ppname.FStar_Ident.idText) bs
          | uu____67349 -> []  in
        let tys = (ml_tyvars, mlt)  in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp  in
        let uu____67357 =
          FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false  in
        match uu____67357 with
        | (env2,uu____67384,uu____67385) ->
            let uu____67388 =
              let uu____67401 = lident_as_mlsymbol ctor.dname  in
              let uu____67403 =
                let uu____67411 = FStar_Extraction_ML_Util.argTypes mlt  in
                FStar_List.zip names1 uu____67411  in
              (uu____67401, uu____67403)  in
            (env2, uu____67388)
         in
      let extract_one_family env1 ind =
        let uu____67472 = binders_as_mlty_binders env1 ind.iparams  in
        match uu____67472 with
        | (env_iparams,vars) ->
            let uu____67516 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor env_iparams vars) env1)
               in
            (match uu____67516 with
             | (env2,ctors) ->
                 let uu____67623 = FStar_Syntax_Util.arrow_formals ind.ityp
                    in
                 (match uu____67623 with
                  | (indices,uu____67665) ->
                      let ml_params =
                        let uu____67690 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____67716  ->
                                    let uu____67724 =
                                      FStar_Util.string_of_int i  in
                                    Prims.op_Hat "'dummyV" uu____67724))
                           in
                        FStar_List.append vars uu____67690  in
                      let tbody =
                        let uu____67729 =
                          FStar_Util.find_opt
                            (fun uu___619_67734  ->
                               match uu___619_67734 with
                               | FStar_Syntax_Syntax.RecordType uu____67736
                                   -> true
                               | uu____67746 -> false) ind.iquals
                           in
                        match uu____67729 with
                        | FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                            let uu____67758 = FStar_List.hd ctors  in
                            (match uu____67758 with
                             | (uu____67783,c_ty) ->
                                 let fields =
                                   FStar_List.map2
                                     (fun id1  ->
                                        fun uu____67827  ->
                                          match uu____67827 with
                                          | (uu____67838,ty) ->
                                              let lid =
                                                FStar_Ident.lid_of_ids
                                                  (FStar_List.append ns [id1])
                                                 in
                                              let uu____67843 =
                                                lident_as_mlsymbol lid  in
                                              (uu____67843, ty)) ids c_ty
                                    in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____67846 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors
                         in
                      let uu____67849 =
                        let uu____67872 = lident_as_mlsymbol ind.iname  in
                        (false, uu____67872, FStar_Pervasives_Native.None,
                          ml_params, (ind.imetadata),
                          (FStar_Pervasives_Native.Some tbody))
                         in
                      (env2, uu____67849)))
         in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____67917,t,uu____67919,uu____67920,uu____67921);
            FStar_Syntax_Syntax.sigrng = uu____67922;
            FStar_Syntax_Syntax.sigquals = uu____67923;
            FStar_Syntax_Syntax.sigmeta = uu____67924;
            FStar_Syntax_Syntax.sigattrs = uu____67925;_}::[],uu____67926),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____67945 = extract_ctor env [] env { dname = l; dtyp = t }
             in
          (match uu____67945 with
           | (env1,ctor) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____67998),quals) ->
          let uu____68012 =
            bundle_as_inductive_families env ses quals
              se.FStar_Syntax_Syntax.sigattrs
             in
          (match uu____68012 with
           | (env1,ifams) ->
               let uu____68031 =
                 FStar_Util.fold_map extract_one_family env1 ifams  in
               (match uu____68031 with
                | (env2,td) -> (env2, [FStar_Extraction_ML_Syntax.MLM_Ty td])))
      | uu____68140 -> failwith "Unexpected signature element"
  
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
             let uu____68198 = FStar_Syntax_Util.head_and_args t  in
             match uu____68198 with
             | (head1,args) ->
                 let uu____68246 =
                   let uu____68248 =
                     FStar_Syntax_Util.is_fvar FStar_Parser_Const.plugin_attr
                       head1
                      in
                   Prims.op_Negation uu____68248  in
                 if uu____68246
                 then FStar_Pervasives_Native.None
                 else
                   (match args with
                    | ({
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_int (s,uu____68267));
                         FStar_Syntax_Syntax.pos = uu____68268;
                         FStar_Syntax_Syntax.vars = uu____68269;_},uu____68270)::[]
                        ->
                        let uu____68309 =
                          let uu____68313 = FStar_Util.int_of_string s  in
                          FStar_Pervasives_Native.Some uu____68313  in
                        FStar_Pervasives_Native.Some uu____68309
                    | uu____68319 ->
                        FStar_Pervasives_Native.Some
                          FStar_Pervasives_Native.None))
         in
      let uu____68334 =
        let uu____68336 = FStar_Options.codegen ()  in
        uu____68336 <> (FStar_Pervasives_Native.Some FStar_Options.Plugin)
         in
      if uu____68334
      then []
      else
        (let uu____68346 = plugin_with_arity se.FStar_Syntax_Syntax.sigattrs
            in
         match uu____68346 with
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
                      let uu____68388 =
                        let uu____68389 = FStar_Ident.string_of_lid fv_lid1
                           in
                        FStar_Extraction_ML_Syntax.MLC_String uu____68389  in
                      FStar_Extraction_ML_Syntax.MLE_Const uu____68388  in
                    let uu____68391 =
                      FStar_Extraction_ML_Util.interpret_plugin_as_term_fun
                        g.FStar_Extraction_ML_UEnv.env_tcenv fv fv_t
                        arity_opt ml_name_str
                       in
                    match uu____68391 with
                    | FStar_Pervasives_Native.Some
                        (interp,nbe_interp,arity,plugin1) ->
                        let uu____68424 =
                          if plugin1
                          then
                            ("FStar_Tactics_Native.register_plugin",
                              [interp; nbe_interp])
                          else
                            ("FStar_Tactics_Native.register_tactic",
                              [interp])
                           in
                        (match uu____68424 with
                         | (register,args) ->
                             let h =
                               let uu____68461 =
                                 let uu____68462 =
                                   let uu____68463 =
                                     FStar_Ident.lid_of_str register  in
                                   FStar_Extraction_ML_Syntax.mlpath_of_lident
                                     uu____68463
                                    in
                                 FStar_Extraction_ML_Syntax.MLE_Name
                                   uu____68462
                                  in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    FStar_Extraction_ML_Syntax.MLTY_Top)
                                 uu____68461
                                in
                             let arity1 =
                               let uu____68465 =
                                 let uu____68466 =
                                   let uu____68478 =
                                     FStar_Util.string_of_int arity  in
                                   (uu____68478,
                                     FStar_Pervasives_Native.None)
                                    in
                                 FStar_Extraction_ML_Syntax.MLC_Int
                                   uu____68466
                                  in
                               FStar_Extraction_ML_Syntax.MLE_Const
                                 uu____68465
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
              | uu____68507 -> []))
  
let rec (extract_sig :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list))
  =
  fun g  ->
    fun se  ->
      FStar_Extraction_ML_UEnv.debug g
        (fun u  ->
           let uu____68535 = FStar_Syntax_Print.sigelt_to_string se  in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____68535);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle uu____68544 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____68553 ->
           extract_bundle g se
       | FStar_Syntax_Syntax.Sig_datacon uu____68570 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           FStar_TypeChecker_Env.is_reifiable_effect
             g.FStar_Extraction_ML_UEnv.env_tcenv
             ed.FStar_Syntax_Syntax.mname
           ->
           let uu____68587 = extract_reifiable_effect g ed  in
           (match uu____68587 with | (env,_iface,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_splice uu____68611 ->
           failwith "impossible: trying to extract splice"
       | FStar_Syntax_Syntax.Sig_new_effect uu____68625 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let uu____68631 =
             extract_type_declaration g lid se.FStar_Syntax_Syntax.sigquals
               se.FStar_Syntax_Syntax.sigattrs univs1 t
              in
           (match uu____68631 with | (env,uu____68647,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____68656) when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let uu____68665 =
             extract_typ_abbrev g se.FStar_Syntax_Syntax.sigquals
               se.FStar_Syntax_Syntax.sigattrs lb
              in
           (match uu____68665 with | (env,uu____68681,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____68690) ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____68701 =
             let uu____68710 =
               FStar_Syntax_Util.extract_attr'
                 FStar_Parser_Const.postprocess_extr_with attrs
                in
             match uu____68710 with
             | FStar_Pervasives_Native.None  ->
                 (attrs, FStar_Pervasives_Native.None)
             | FStar_Pervasives_Native.Some
                 (ats,(tau,FStar_Pervasives_Native.None )::uu____68739) ->
                 (ats, (FStar_Pervasives_Native.Some tau))
             | FStar_Pervasives_Native.Some (ats,args) ->
                 (FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng
                    (FStar_Errors.Warning_UnrecognizedAttribute,
                      "Ill-formed application of `postprocess_for_extraction_with`");
                  (attrs, FStar_Pervasives_Native.None))
              in
           (match uu____68701 with
            | (attrs1,post_tau) ->
                let postprocess_lb tau lb =
                  let lbdef =
                    FStar_TypeChecker_Env.postprocess
                      g.FStar_Extraction_ML_UEnv.env_tcenv tau
                      lb.FStar_Syntax_Syntax.lbtyp
                      lb.FStar_Syntax_Syntax.lbdef
                     in
                  let uu___1403_68825 = lb  in
                  {
                    FStar_Syntax_Syntax.lbname =
                      (uu___1403_68825.FStar_Syntax_Syntax.lbname);
                    FStar_Syntax_Syntax.lbunivs =
                      (uu___1403_68825.FStar_Syntax_Syntax.lbunivs);
                    FStar_Syntax_Syntax.lbtyp =
                      (uu___1403_68825.FStar_Syntax_Syntax.lbtyp);
                    FStar_Syntax_Syntax.lbeff =
                      (uu___1403_68825.FStar_Syntax_Syntax.lbeff);
                    FStar_Syntax_Syntax.lbdef = lbdef;
                    FStar_Syntax_Syntax.lbattrs =
                      (uu___1403_68825.FStar_Syntax_Syntax.lbattrs);
                    FStar_Syntax_Syntax.lbpos =
                      (uu___1403_68825.FStar_Syntax_Syntax.lbpos)
                  }  in
                let lbs1 =
                  let uu____68834 =
                    match post_tau with
                    | FStar_Pervasives_Native.Some tau ->
                        FStar_List.map (postprocess_lb tau)
                          (FStar_Pervasives_Native.snd lbs)
                    | FStar_Pervasives_Native.None  ->
                        FStar_Pervasives_Native.snd lbs
                     in
                  ((FStar_Pervasives_Native.fst lbs), uu____68834)  in
                let uu____68852 =
                  let uu____68859 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_let
                         (lbs1, FStar_Syntax_Util.exp_false_bool))
                      FStar_Pervasives_Native.None
                      se.FStar_Syntax_Syntax.sigrng
                     in
                  FStar_Extraction_ML_Term.term_as_mlexpr g uu____68859  in
                (match uu____68852 with
                 | (ml_let,uu____68876,uu____68877) ->
                     (match ml_let.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Let
                          ((flavor,bindings),uu____68886) ->
                          let flags = FStar_List.choose flag_of_qual quals
                             in
                          let flags' = extract_metadata attrs1  in
                          let uu____68903 =
                            FStar_List.fold_left2
                              (fun uu____68929  ->
                                 fun ml_lb  ->
                                   fun uu____68931  ->
                                     match (uu____68929, uu____68931) with
                                     | ((env,ml_lbs),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbname;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uu____68953;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = t;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____68955;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = uu____68956;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____68957;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____68958;_})
                                         ->
                                         let uu____68983 =
                                           FStar_All.pipe_right
                                             ml_lb.FStar_Extraction_ML_Syntax.mllb_meta
                                             (FStar_List.contains
                                                FStar_Extraction_ML_Syntax.Erased)
                                            in
                                         if uu____68983
                                         then (env, ml_lbs)
                                         else
                                           (let lb_lid =
                                              let uu____69000 =
                                                let uu____69003 =
                                                  FStar_Util.right lbname  in
                                                uu____69003.FStar_Syntax_Syntax.fv_name
                                                 in
                                              uu____69000.FStar_Syntax_Syntax.v
                                               in
                                            let flags'' =
                                              let uu____69007 =
                                                let uu____69008 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____69008.FStar_Syntax_Syntax.n
                                                 in
                                              match uu____69007 with
                                              | FStar_Syntax_Syntax.Tm_arrow
                                                  (uu____69013,{
                                                                 FStar_Syntax_Syntax.n
                                                                   =
                                                                   FStar_Syntax_Syntax.Comp
                                                                   {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____69014;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    = e;
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    =
                                                                    uu____69016;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____69017;
                                                                    FStar_Syntax_Syntax.flags
                                                                    =
                                                                    uu____69018;_};
                                                                 FStar_Syntax_Syntax.pos
                                                                   =
                                                                   uu____69019;
                                                                 FStar_Syntax_Syntax.vars
                                                                   =
                                                                   uu____69020;_})
                                                  when
                                                  let uu____69055 =
                                                    FStar_Ident.string_of_lid
                                                      e
                                                     in
                                                  uu____69055 =
                                                    "FStar.HyperStack.ST.StackInline"
                                                  ->
                                                  [FStar_Extraction_ML_Syntax.StackInline]
                                              | uu____69059 -> []  in
                                            let meta =
                                              FStar_List.append flags
                                                (FStar_List.append flags'
                                                   flags'')
                                               in
                                            let ml_lb1 =
                                              let uu___1451_69064 = ml_lb  in
                                              {
                                                FStar_Extraction_ML_Syntax.mllb_name
                                                  =
                                                  (uu___1451_69064.FStar_Extraction_ML_Syntax.mllb_name);
                                                FStar_Extraction_ML_Syntax.mllb_tysc
                                                  =
                                                  (uu___1451_69064.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                FStar_Extraction_ML_Syntax.mllb_add_unit
                                                  =
                                                  (uu___1451_69064.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                FStar_Extraction_ML_Syntax.mllb_def
                                                  =
                                                  (uu___1451_69064.FStar_Extraction_ML_Syntax.mllb_def);
                                                FStar_Extraction_ML_Syntax.mllb_meta
                                                  = meta;
                                                FStar_Extraction_ML_Syntax.print_typ
                                                  =
                                                  (uu___1451_69064.FStar_Extraction_ML_Syntax.print_typ)
                                              }  in
                                            let uu____69065 =
                                              let uu____69070 =
                                                FStar_All.pipe_right quals
                                                  (FStar_Util.for_some
                                                     (fun uu___620_69077  ->
                                                        match uu___620_69077
                                                        with
                                                        | FStar_Syntax_Syntax.Projector
                                                            uu____69079 ->
                                                            true
                                                        | uu____69085 ->
                                                            false))
                                                 in
                                              if uu____69070
                                              then
                                                let mname =
                                                  let uu____69101 =
                                                    mangle_projector_lid
                                                      lb_lid
                                                     in
                                                  FStar_All.pipe_right
                                                    uu____69101
                                                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                                                   in
                                                let uu____69110 =
                                                  let uu____69118 =
                                                    FStar_Util.right lbname
                                                     in
                                                  let uu____69119 =
                                                    FStar_Util.must
                                                      ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc
                                                     in
                                                  FStar_Extraction_ML_UEnv.extend_fv'
                                                    env uu____69118 mname
                                                    uu____69119
                                                    ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                                    false
                                                   in
                                                match uu____69110 with
                                                | (env1,uu____69126,uu____69127)
                                                    ->
                                                    (env1,
                                                      (let uu___1464_69131 =
                                                         ml_lb1  in
                                                       {
                                                         FStar_Extraction_ML_Syntax.mllb_name
                                                           =
                                                           (FStar_Pervasives_Native.snd
                                                              mname);
                                                         FStar_Extraction_ML_Syntax.mllb_tysc
                                                           =
                                                           (uu___1464_69131.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                         FStar_Extraction_ML_Syntax.mllb_add_unit
                                                           =
                                                           (uu___1464_69131.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                         FStar_Extraction_ML_Syntax.mllb_def
                                                           =
                                                           (uu___1464_69131.FStar_Extraction_ML_Syntax.mllb_def);
                                                         FStar_Extraction_ML_Syntax.mllb_meta
                                                           =
                                                           (uu___1464_69131.FStar_Extraction_ML_Syntax.mllb_meta);
                                                         FStar_Extraction_ML_Syntax.print_typ
                                                           =
                                                           (uu___1464_69131.FStar_Extraction_ML_Syntax.print_typ)
                                                       }))
                                              else
                                                (let uu____69138 =
                                                   let uu____69146 =
                                                     FStar_Util.must
                                                       ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc
                                                      in
                                                   FStar_Extraction_ML_UEnv.extend_lb
                                                     env lbname t uu____69146
                                                     ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                                     false
                                                    in
                                                 match uu____69138 with
                                                 | (env1,uu____69153,uu____69154)
                                                     -> (env1, ml_lb1))
                                               in
                                            match uu____69065 with
                                            | (g1,ml_lb2) ->
                                                (g1, (ml_lb2 :: ml_lbs))))
                              (g, []) bindings
                              (FStar_Pervasives_Native.snd lbs1)
                             in
                          (match uu____68903 with
                           | (g1,ml_lbs') ->
                               let uu____69184 =
                                 let uu____69187 =
                                   let uu____69190 =
                                     let uu____69191 =
                                       FStar_Extraction_ML_Util.mlloc_of_range
                                         se.FStar_Syntax_Syntax.sigrng
                                        in
                                     FStar_Extraction_ML_Syntax.MLM_Loc
                                       uu____69191
                                      in
                                   [uu____69190;
                                   FStar_Extraction_ML_Syntax.MLM_Let
                                     (flavor, (FStar_List.rev ml_lbs'))]
                                    in
                                 let uu____69194 =
                                   maybe_register_plugin g1 se  in
                                 FStar_List.append uu____69187 uu____69194
                                  in
                               (g1, uu____69184))
                      | uu____69199 ->
                          let uu____69200 =
                            let uu____69202 =
                              FStar_Extraction_ML_Code.string_of_mlexpr
                                g.FStar_Extraction_ML_UEnv.currentModule
                                ml_let
                               in
                            FStar_Util.format1
                              "Impossible: Translated a let to a non-let: %s"
                              uu____69202
                             in
                          failwith uu____69200)))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____69212,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____69217 =
             (FStar_All.pipe_right quals
                (FStar_List.contains FStar_Syntax_Syntax.Assumption))
               &&
               (let uu____69223 =
                  FStar_TypeChecker_Util.must_erase_for_extraction
                    g.FStar_Extraction_ML_UEnv.env_tcenv t
                   in
                Prims.op_Negation uu____69223)
              in
           if uu____69217
           then
             let always_fail1 =
               let uu___1484_69233 = se  in
               let uu____69234 =
                 let uu____69235 =
                   let uu____69242 =
                     let uu____69243 =
                       let uu____69246 = always_fail lid t  in [uu____69246]
                        in
                     (false, uu____69243)  in
                   (uu____69242, [])  in
                 FStar_Syntax_Syntax.Sig_let uu____69235  in
               {
                 FStar_Syntax_Syntax.sigel = uu____69234;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___1484_69233.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___1484_69233.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___1484_69233.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___1484_69233.FStar_Syntax_Syntax.sigattrs)
               }  in
             let uu____69253 = extract_sig g always_fail1  in
             (match uu____69253 with
              | (g1,mlm) ->
                  let uu____69272 =
                    FStar_Util.find_map quals
                      (fun uu___621_69277  ->
                         match uu___621_69277 with
                         | FStar_Syntax_Syntax.Discriminator l ->
                             FStar_Pervasives_Native.Some l
                         | uu____69281 -> FStar_Pervasives_Native.None)
                     in
                  (match uu____69272 with
                   | FStar_Pervasives_Native.Some l ->
                       let uu____69289 =
                         let uu____69292 =
                           let uu____69293 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng
                              in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____69293  in
                         let uu____69294 =
                           let uu____69297 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l
                              in
                           [uu____69297]  in
                         uu____69292 :: uu____69294  in
                       (g1, uu____69289)
                   | uu____69300 ->
                       let uu____69303 =
                         FStar_Util.find_map quals
                           (fun uu___622_69309  ->
                              match uu___622_69309 with
                              | FStar_Syntax_Syntax.Projector (l,uu____69313)
                                  -> FStar_Pervasives_Native.Some l
                              | uu____69314 -> FStar_Pervasives_Native.None)
                          in
                       (match uu____69303 with
                        | FStar_Pervasives_Native.Some uu____69321 ->
                            (g1, [])
                        | uu____69324 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____69334 = FStar_Extraction_ML_Term.term_as_mlexpr g e  in
           (match uu____69334 with
            | (ml_main,uu____69348,uu____69349) ->
                let uu____69350 =
                  let uu____69353 =
                    let uu____69354 =
                      FStar_Extraction_ML_Util.mlloc_of_range
                        se.FStar_Syntax_Syntax.sigrng
                       in
                    FStar_Extraction_ML_Syntax.MLM_Loc uu____69354  in
                  [uu____69353; FStar_Extraction_ML_Syntax.MLM_Top ml_main]
                   in
                (g, uu____69350))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____69357 ->
           failwith "impossible -- removed by tc.fs"
       | FStar_Syntax_Syntax.Sig_assume uu____69365 -> (g, [])
       | FStar_Syntax_Syntax.Sig_sub_effect uu____69374 -> (g, [])
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____69377 -> (g, [])
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
      let uu____69419 = FStar_Options.restore_cmd_line_options true  in
      let name =
        FStar_Extraction_ML_Syntax.mlpath_of_lident
          m.FStar_Syntax_Syntax.name
         in
      let g1 =
        let uu___1527_69423 = g  in
        let uu____69424 =
          FStar_TypeChecker_Env.set_current_module
            g.FStar_Extraction_ML_UEnv.env_tcenv m.FStar_Syntax_Syntax.name
           in
        {
          FStar_Extraction_ML_UEnv.env_tcenv = uu____69424;
          FStar_Extraction_ML_UEnv.env_bindings =
            (uu___1527_69423.FStar_Extraction_ML_UEnv.env_bindings);
          FStar_Extraction_ML_UEnv.tydefs =
            (uu___1527_69423.FStar_Extraction_ML_UEnv.tydefs);
          FStar_Extraction_ML_UEnv.type_names =
            (uu___1527_69423.FStar_Extraction_ML_UEnv.type_names);
          FStar_Extraction_ML_UEnv.currentModule = name
        }  in
      let uu____69425 =
        FStar_Util.fold_map
          (fun g2  ->
             fun se  ->
               let uu____69444 =
                 FStar_Options.debug_module
                   (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                  in
               if uu____69444
               then
                 let nm =
                   let uu____69455 =
                     FStar_All.pipe_right
                       (FStar_Syntax_Util.lids_of_sigelt se)
                       (FStar_List.map FStar_Ident.string_of_lid)
                      in
                   FStar_All.pipe_right uu____69455
                     (FStar_String.concat ", ")
                    in
                 (FStar_Util.print1 "+++About to extract {%s}\n" nm;
                  (let uu____69472 =
                     FStar_Util.format1 "---Extracted {%s}" nm  in
                   FStar_Util.measure_execution_time uu____69472
                     (fun uu____69482  -> extract_sig g2 se)))
               else extract_sig g2 se) g1 m.FStar_Syntax_Syntax.declarations
         in
      match uu____69425 with
      | (g2,sigs) ->
          let mlm = FStar_List.flatten sigs  in
          let is_kremlin =
            let uu____69504 = FStar_Options.codegen ()  in
            uu____69504 =
              (FStar_Pervasives_Native.Some FStar_Options.Kremlin)
             in
          if
            ((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims") &&
              (is_kremlin ||
                 (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface))
          then
            ((let uu____69519 =
                let uu____69521 = FStar_Options.silent ()  in
                Prims.op_Negation uu____69521  in
              if uu____69519
              then
                let uu____69524 =
                  FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
                FStar_Util.print1 "Extracted module %s\n" uu____69524
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
      (let uu____69599 = FStar_Options.restore_cmd_line_options true  in
       FStar_All.pipe_left (fun a2  -> ()) uu____69599);
      (let uu____69602 =
         let uu____69604 =
           FStar_Options.should_extract
             (m.FStar_Syntax_Syntax.name).FStar_Ident.str
            in
         Prims.op_Negation uu____69604  in
       if uu____69602
       then
         let uu____69607 =
           let uu____69609 =
             FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
           FStar_Util.format1
             "Extract called on a module %s that should not be extracted"
             uu____69609
            in
         failwith uu____69607
       else ());
      (let uu____69614 = FStar_Options.interactive ()  in
       if uu____69614
       then (g, FStar_Pervasives_Native.None)
       else
         (let res =
            let uu____69634 = FStar_Options.debug_any ()  in
            if uu____69634
            then
              let msg =
                let uu____69645 =
                  FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name
                   in
                FStar_Util.format1 "Extracting module %s\n" uu____69645  in
              FStar_Util.measure_execution_time msg
                (fun uu____69655  -> extract' g m)
            else extract' g m  in
          (let uu____69659 = FStar_Options.restore_cmd_line_options true  in
           FStar_All.pipe_left (fun a3  -> ()) uu____69659);
          res))
  
open Prims
type env_t = FStar_Extraction_ML_UEnv.uenv
let (fail_exp :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun lid  ->
    fun t  ->
      let uu____63780 =
        let uu____63787 =
          let uu____63788 =
            let uu____63805 =
              FStar_Syntax_Syntax.fvar FStar_Parser_Const.failwith_lid
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            let uu____63808 =
              let uu____63819 = FStar_Syntax_Syntax.iarg t  in
              let uu____63828 =
                let uu____63839 =
                  let uu____63848 =
                    let uu____63849 =
                      let uu____63856 =
                        let uu____63857 =
                          let uu____63858 =
                            let uu____63864 =
                              let uu____63866 =
                                FStar_Syntax_Print.lid_to_string lid  in
                              Prims.op_Hat "Not yet implemented:" uu____63866
                               in
                            (uu____63864, FStar_Range.dummyRange)  in
                          FStar_Const.Const_string uu____63858  in
                        FStar_Syntax_Syntax.Tm_constant uu____63857  in
                      FStar_Syntax_Syntax.mk uu____63856  in
                    uu____63849 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange
                     in
                  FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____63848
                   in
                [uu____63839]  in
              uu____63819 :: uu____63828  in
            (uu____63805, uu____63808)  in
          FStar_Syntax_Syntax.Tm_app uu____63788  in
        FStar_Syntax_Syntax.mk uu____63787  in
      uu____63780 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (always_fail :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.letbinding)
  =
  fun lid  ->
    fun t  ->
      let imp =
        let uu____63932 = FStar_Syntax_Util.arrow_formals t  in
        match uu____63932 with
        | ([],t1) ->
            let b =
              let uu____63975 =
                FStar_Syntax_Syntax.gen_bv "_" FStar_Pervasives_Native.None
                  t1
                 in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____63975
               in
            let uu____63983 = fail_exp lid t1  in
            FStar_Syntax_Util.abs [b] uu____63983
              FStar_Pervasives_Native.None
        | (bs,t1) ->
            let uu____64020 = fail_exp lid t1  in
            FStar_Syntax_Util.abs bs uu____64020 FStar_Pervasives_Native.None
         in
      let lb =
        let uu____64024 =
          let uu____64029 =
            FStar_Syntax_Syntax.lid_as_fv lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Util.Inr uu____64029  in
        {
          FStar_Syntax_Syntax.lbname = uu____64024;
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
  'Auu____64051 . 'Auu____64051 Prims.list -> ('Auu____64051 * 'Auu____64051)
  =
  fun uu___612_64062  ->
    match uu___612_64062 with
    | a::b::[] -> (a, b)
    | uu____64067 -> failwith "Expected a list with 2 elements"
  
let (flag_of_qual :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option)
  =
  fun uu___613_64082  ->
    match uu___613_64082 with
    | FStar_Syntax_Syntax.Assumption  ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Assumed
    | FStar_Syntax_Syntax.Private  ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Private
    | FStar_Syntax_Syntax.NoExtract  ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.NoExtract
    | uu____64085 -> FStar_Pervasives_Native.None
  
let rec (extract_meta :
  FStar_Syntax_Syntax.term ->
    FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option)
  =
  fun x  ->
    let uu____64094 = FStar_Syntax_Subst.compress x  in
    match uu____64094 with
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
        FStar_Syntax_Syntax.pos = uu____64098;
        FStar_Syntax_Syntax.vars = uu____64099;_} ->
        let uu____64102 =
          let uu____64104 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____64104  in
        (match uu____64102 with
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
         | uu____64114 -> FStar_Pervasives_Native.None)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____64117;
             FStar_Syntax_Syntax.vars = uu____64118;_},({
                                                          FStar_Syntax_Syntax.n
                                                            =
                                                            FStar_Syntax_Syntax.Tm_constant
                                                            (FStar_Const.Const_string
                                                            (s,uu____64120));
                                                          FStar_Syntax_Syntax.pos
                                                            = uu____64121;
                                                          FStar_Syntax_Syntax.vars
                                                            = uu____64122;_},uu____64123)::[]);
        FStar_Syntax_Syntax.pos = uu____64124;
        FStar_Syntax_Syntax.vars = uu____64125;_} ->
        let uu____64168 =
          let uu____64170 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____64170  in
        (match uu____64168 with
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
         | uu____64179 -> FStar_Pervasives_Native.None)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("KremlinPrivate",uu____64181));
        FStar_Syntax_Syntax.pos = uu____64182;
        FStar_Syntax_Syntax.vars = uu____64183;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Private
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("c_inline",uu____64188));
        FStar_Syntax_Syntax.pos = uu____64189;
        FStar_Syntax_Syntax.vars = uu____64190;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.CInline
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("substitute",uu____64195));
        FStar_Syntax_Syntax.pos = uu____64196;
        FStar_Syntax_Syntax.vars = uu____64197;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Substitute
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_meta (x1,uu____64203);
        FStar_Syntax_Syntax.pos = uu____64204;
        FStar_Syntax_Syntax.vars = uu____64205;_} -> extract_meta x1
    | uu____64212 -> FStar_Pervasives_Native.None
  
let (extract_metadata :
  FStar_Syntax_Syntax.term Prims.list ->
    FStar_Extraction_ML_Syntax.meta Prims.list)
  = fun metas  -> FStar_List.choose extract_meta metas 
let binders_as_mlty_binders :
  'Auu____64232 .
    FStar_Extraction_ML_UEnv.uenv ->
      (FStar_Syntax_Syntax.bv * 'Auu____64232) Prims.list ->
        (FStar_Extraction_ML_UEnv.uenv * Prims.string Prims.list)
  =
  fun env  ->
    fun bs  ->
      FStar_Util.fold_map
        (fun env1  ->
           fun uu____64274  ->
             match uu____64274 with
             | (bv,uu____64285) ->
                 let uu____64286 =
                   let uu____64287 =
                     let uu____64290 =
                       let uu____64291 =
                         FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv  in
                       FStar_Extraction_ML_Syntax.MLTY_Var uu____64291  in
                     FStar_Pervasives_Native.Some uu____64290  in
                   FStar_Extraction_ML_UEnv.extend_ty env1 bv uu____64287  in
                 let uu____64293 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv
                    in
                 (uu____64286, uu____64293)) env bs
  
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
    let uu____64494 = FStar_Syntax_Print.lid_to_string i.iname  in
    let uu____64496 = FStar_Syntax_Print.binders_to_string " " i.iparams  in
    let uu____64499 = FStar_Syntax_Print.term_to_string i.ityp  in
    let uu____64501 =
      let uu____64503 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d  ->
                let uu____64517 = FStar_Syntax_Print.lid_to_string d.dname
                   in
                let uu____64519 =
                  let uu____64521 = FStar_Syntax_Print.term_to_string d.dtyp
                     in
                  Prims.op_Hat " : " uu____64521  in
                Prims.op_Hat uu____64517 uu____64519))
         in
      FStar_All.pipe_right uu____64503 (FStar_String.concat "\n\t\t")  in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____64494 uu____64496
      uu____64499 uu____64501
  
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
          let uu____64575 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun se  ->
                   match se.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,_us,bs,t,_mut_i,datas) ->
                       let uu____64623 = FStar_Syntax_Subst.open_term bs t
                          in
                       (match uu____64623 with
                        | (bs1,t1) ->
                            let datas1 =
                              FStar_All.pipe_right ses
                                (FStar_List.collect
                                   (fun se1  ->
                                      match se1.FStar_Syntax_Syntax.sigel
                                      with
                                      | FStar_Syntax_Syntax.Sig_datacon
                                          (d,uu____64662,t2,l',nparams,uu____64666)
                                          when FStar_Ident.lid_equals l l' ->
                                          let uu____64673 =
                                            FStar_Syntax_Util.arrow_formals
                                              t2
                                             in
                                          (match uu____64673 with
                                           | (bs',body) ->
                                               let uu____64712 =
                                                 FStar_Util.first_N
                                                   (FStar_List.length bs1)
                                                   bs'
                                                  in
                                               (match uu____64712 with
                                                | (bs_params,rest) ->
                                                    let subst1 =
                                                      FStar_List.map2
                                                        (fun uu____64803  ->
                                                           fun uu____64804 
                                                             ->
                                                             match (uu____64803,
                                                                    uu____64804)
                                                             with
                                                             | ((b',uu____64830),
                                                                (b,uu____64832))
                                                                 ->
                                                                 let uu____64853
                                                                   =
                                                                   let uu____64860
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    b  in
                                                                   (b',
                                                                    uu____64860)
                                                                    in
                                                                 FStar_Syntax_Syntax.NT
                                                                   uu____64853)
                                                        bs_params bs1
                                                       in
                                                    let t3 =
                                                      let uu____64866 =
                                                        let uu____64867 =
                                                          FStar_Syntax_Syntax.mk_Total
                                                            body
                                                           in
                                                        FStar_Syntax_Util.arrow
                                                          rest uu____64867
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____64866
                                                        (FStar_Syntax_Subst.subst
                                                           subst1)
                                                       in
                                                    [{ dname = d; dtyp = t3 }]))
                                      | uu____64870 -> []))
                               in
                            let metadata =
                              let uu____64874 =
                                extract_metadata
                                  (FStar_List.append
                                     se.FStar_Syntax_Syntax.sigattrs attrs)
                                 in
                              let uu____64877 =
                                FStar_List.choose flag_of_qual quals  in
                              FStar_List.append uu____64874 uu____64877  in
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
                   | uu____64884 -> (env1, [])) env ses
             in
          match uu____64575 with
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
    let uu___820_65064 = empty_iface  in
    {
      iface_module_name = (uu___820_65064.iface_module_name);
      iface_bindings = fvs;
      iface_tydefs = (uu___820_65064.iface_tydefs);
      iface_type_names = (uu___820_65064.iface_type_names)
    }
  
let (iface_of_tydefs : FStar_Extraction_ML_UEnv.tydef Prims.list -> iface) =
  fun tds  ->
    let uu___823_65075 = empty_iface  in
    let uu____65076 =
      FStar_List.map (fun td  -> td.FStar_Extraction_ML_UEnv.tydef_fv) tds
       in
    {
      iface_module_name = (uu___823_65075.iface_module_name);
      iface_bindings = (uu___823_65075.iface_bindings);
      iface_tydefs = tds;
      iface_type_names = uu____65076
    }
  
let (iface_of_type_names : FStar_Syntax_Syntax.fv Prims.list -> iface) =
  fun fvs  ->
    let uu___827_65091 = empty_iface  in
    {
      iface_module_name = (uu___827_65091.iface_module_name);
      iface_bindings = (uu___827_65091.iface_bindings);
      iface_tydefs = (uu___827_65091.iface_tydefs);
      iface_type_names = fvs
    }
  
let (iface_union : iface -> iface -> iface) =
  fun if1  ->
    fun if2  ->
      let uu____65103 =
        if if1.iface_module_name <> if1.iface_module_name
        then failwith "Union not defined"
        else if1.iface_module_name  in
      {
        iface_module_name = uu____65103;
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
  'Auu____65148 .
    FStar_Extraction_ML_Syntax.mlpath ->
      ('Auu____65148 * FStar_Extraction_ML_Syntax.mlty) -> Prims.string
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
      let uu____65180 =
        FStar_Extraction_ML_Code.string_of_mlexpr cm
          e.FStar_Extraction_ML_UEnv.exp_b_expr
         in
      let uu____65182 =
        tscheme_to_string cm e.FStar_Extraction_ML_UEnv.exp_b_tscheme  in
      let uu____65184 =
        FStar_Util.string_of_bool e.FStar_Extraction_ML_UEnv.exp_b_inst_ok
         in
      FStar_Util.format4
        "{\n\texp_b_name = %s\n\texp_b_expr = %s\n\texp_b_tscheme = %s\n\texp_b_is_rec = %s }"
        e.FStar_Extraction_ML_UEnv.exp_b_name uu____65180 uu____65182
        uu____65184
  
let (print_binding :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_UEnv.exp_binding) ->
      Prims.string)
  =
  fun cm  ->
    fun uu____65202  ->
      match uu____65202 with
      | (fv,exp_binding) ->
          let uu____65210 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____65212 = print_exp_binding cm exp_binding  in
          FStar_Util.format2 "(%s, %s)" uu____65210 uu____65212
  
let (print_tydef :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_UEnv.tydef -> Prims.string)
  =
  fun cm  ->
    fun tydef  ->
      let uu____65227 =
        FStar_Syntax_Print.fv_to_string
          tydef.FStar_Extraction_ML_UEnv.tydef_fv
         in
      let uu____65229 =
        tscheme_to_string cm tydef.FStar_Extraction_ML_UEnv.tydef_def  in
      FStar_Util.format2 "(%s, %s)" uu____65227 uu____65229
  
let (iface_to_string : iface -> Prims.string) =
  fun iface1  ->
    let cm = iface1.iface_module_name  in
    let print_type_name tn = FStar_Syntax_Print.fv_to_string tn  in
    let uu____65247 =
      let uu____65249 =
        FStar_List.map (print_binding cm) iface1.iface_bindings  in
      FStar_All.pipe_right uu____65249 (FStar_String.concat "\n")  in
    let uu____65263 =
      let uu____65265 = FStar_List.map (print_tydef cm) iface1.iface_tydefs
         in
      FStar_All.pipe_right uu____65265 (FStar_String.concat "\n")  in
    let uu____65275 =
      let uu____65277 =
        FStar_List.map print_type_name iface1.iface_type_names  in
      FStar_All.pipe_right uu____65277 (FStar_String.concat "\n")  in
    FStar_Util.format4
      "Interface %s = {\niface_bindings=\n%s;\n\niface_tydefs=\n%s;\n\niface_type_names=%s;\n}"
      (mlpath_to_string iface1.iface_module_name) uu____65247 uu____65263
      uu____65275
  
let (gamma_to_string : FStar_Extraction_ML_UEnv.uenv -> Prims.string) =
  fun env  ->
    let cm = env.FStar_Extraction_ML_UEnv.currentModule  in
    let gamma =
      FStar_List.collect
        (fun uu___614_65310  ->
           match uu___614_65310 with
           | FStar_Extraction_ML_UEnv.Fv (b,e) -> [(b, e)]
           | uu____65327 -> []) env.FStar_Extraction_ML_UEnv.env_bindings
       in
    let uu____65332 =
      let uu____65334 = FStar_List.map (print_binding cm) gamma  in
      FStar_All.pipe_right uu____65334 (FStar_String.concat "\n")  in
    FStar_Util.format1 "Gamma = {\n %s }" uu____65332
  
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
          let uu____65394 =
            let uu____65403 =
              FStar_TypeChecker_Env.open_universes_in
                env.FStar_Extraction_ML_UEnv.env_tcenv
                lb.FStar_Syntax_Syntax.lbunivs
                [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp]
               in
            match uu____65403 with
            | (tcenv,uu____65421,def_typ) ->
                let uu____65427 = as_pair def_typ  in (tcenv, uu____65427)
             in
          match uu____65394 with
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
                let uu____65458 =
                  let uu____65459 = FStar_Syntax_Subst.compress lbdef1  in
                  FStar_All.pipe_right uu____65459 FStar_Syntax_Util.unmeta
                   in
                FStar_All.pipe_right uu____65458 FStar_Syntax_Util.un_uinst
                 in
              let def1 =
                match def.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_abs uu____65467 ->
                    FStar_Extraction_ML_Term.normalize_abs def
                | uu____65486 -> def  in
              let uu____65487 =
                match def1.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____65498) ->
                    FStar_Syntax_Subst.open_term bs body
                | uu____65523 -> ([], def1)  in
              (match uu____65487 with
               | (bs,body) ->
                   let assumed =
                     FStar_Util.for_some
                       (fun uu___615_65543  ->
                          match uu___615_65543 with
                          | FStar_Syntax_Syntax.Assumption  -> true
                          | uu____65546 -> false) quals
                      in
                   let uu____65548 = binders_as_mlty_binders env bs  in
                   (match uu____65548 with
                    | (env1,ml_bs) ->
                        let body1 =
                          let uu____65575 =
                            FStar_Extraction_ML_Term.term_as_mlty env1 body
                             in
                          FStar_All.pipe_right uu____65575
                            (FStar_Extraction_ML_Util.eraseTypeDeep
                               (FStar_Extraction_ML_Util.udelta_unfold env1))
                           in
                        let mangled_projector =
                          let uu____65580 =
                            FStar_All.pipe_right quals
                              (FStar_Util.for_some
                                 (fun uu___616_65587  ->
                                    match uu___616_65587 with
                                    | FStar_Syntax_Syntax.Projector
                                        uu____65589 -> true
                                    | uu____65595 -> false))
                             in
                          if uu____65580
                          then
                            let mname = mangle_projector_lid lid  in
                            FStar_Pervasives_Native.Some
                              ((mname.FStar_Ident.ident).FStar_Ident.idText)
                          else FStar_Pervasives_Native.None  in
                        let metadata =
                          let uu____65609 = extract_metadata attrs  in
                          let uu____65612 =
                            FStar_List.choose flag_of_qual quals  in
                          FStar_List.append uu____65609 uu____65612  in
                        let td =
                          let uu____65635 = lident_as_mlsymbol lid  in
                          (assumed, uu____65635, mangled_projector, ml_bs,
                            metadata,
                            (FStar_Pervasives_Native.Some
                               (FStar_Extraction_ML_Syntax.MLTD_Abbrev body1)))
                           in
                        let def2 =
                          let uu____65647 =
                            let uu____65648 =
                              let uu____65649 = FStar_Ident.range_of_lid lid
                                 in
                              FStar_Extraction_ML_Util.mlloc_of_range
                                uu____65649
                               in
                            FStar_Extraction_ML_Syntax.MLM_Loc uu____65648
                             in
                          [uu____65647;
                          FStar_Extraction_ML_Syntax.MLM_Ty [td]]  in
                        let uu____65650 =
                          let uu____65655 =
                            FStar_All.pipe_right quals
                              (FStar_Util.for_some
                                 (fun uu___617_65661  ->
                                    match uu___617_65661 with
                                    | FStar_Syntax_Syntax.Assumption  -> true
                                    | FStar_Syntax_Syntax.New  -> true
                                    | uu____65665 -> false))
                             in
                          if uu____65655
                          then
                            let uu____65672 =
                              FStar_Extraction_ML_UEnv.extend_type_name env
                                fv
                               in
                            (uu____65672, (iface_of_type_names [fv]))
                          else
                            (let uu____65675 =
                               FStar_Extraction_ML_UEnv.extend_tydef env fv
                                 td
                                in
                             match uu____65675 with
                             | (env2,tydef) ->
                                 let uu____65686 = iface_of_tydefs [tydef]
                                    in
                                 (env2, uu____65686))
                           in
                        (match uu____65650 with
                         | (env2,iface1) -> (env2, iface1, def2))))
  
let (extract_bundle_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt -> (env_t * iface))
  =
  fun env  ->
    fun se  ->
      let extract_ctor env_iparams ml_tyvars env1 ctor =
        let mlt =
          let uu____65762 =
            FStar_Extraction_ML_Term.term_as_mlty env_iparams ctor.dtyp  in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env_iparams) uu____65762
           in
        let tys = (ml_tyvars, mlt)  in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp  in
        let uu____65769 =
          FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false  in
        match uu____65769 with | (env2,uu____65788,b) -> (env2, (fvv, b))  in
      let extract_one_family env1 ind =
        let uu____65827 = binders_as_mlty_binders env1 ind.iparams  in
        match uu____65827 with
        | (env_iparams,vars) ->
            let uu____65855 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor env_iparams vars) env1)
               in
            (match uu____65855 with | (env2,ctors) -> (env2, ctors))
         in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____65919,t,uu____65921,uu____65922,uu____65923);
            FStar_Syntax_Syntax.sigrng = uu____65924;
            FStar_Syntax_Syntax.sigquals = uu____65925;
            FStar_Syntax_Syntax.sigmeta = uu____65926;
            FStar_Syntax_Syntax.sigattrs = uu____65927;_}::[],uu____65928),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____65947 = extract_ctor env [] env { dname = l; dtyp = t }
             in
          (match uu____65947 with
           | (env1,ctor) -> (env1, (iface_of_bindings [ctor])))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____65980),quals) ->
          let uu____65994 =
            bundle_as_inductive_families env ses quals
              se.FStar_Syntax_Syntax.sigattrs
             in
          (match uu____65994 with
           | (env1,ifams) ->
               let uu____66011 =
                 FStar_Util.fold_map extract_one_family env1 ifams  in
               (match uu____66011 with
                | (env2,td) ->
                    let uu____66052 =
                      let uu____66053 =
                        let uu____66054 =
                          FStar_List.map (fun x  -> x.ifv) ifams  in
                        iface_of_type_names uu____66054  in
                      iface_union uu____66053
                        (iface_of_bindings (FStar_List.flatten td))
                       in
                    (env2, uu____66052)))
      | uu____66063 -> failwith "Unexpected signature element"
  
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
              let uu____66138 =
                let uu____66140 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun uu___618_66146  ->
                          match uu___618_66146 with
                          | FStar_Syntax_Syntax.Assumption  -> true
                          | uu____66149 -> false))
                   in
                Prims.op_Negation uu____66140  in
              if uu____66138
              then (g, empty_iface, [])
              else
                (let uu____66164 = FStar_Syntax_Util.arrow_formals t  in
                 match uu____66164 with
                 | (bs,uu____66188) ->
                     let fv =
                       FStar_Syntax_Syntax.lid_as_fv lid
                         FStar_Syntax_Syntax.delta_constant
                         FStar_Pervasives_Native.None
                        in
                     let lb =
                       let uu____66211 =
                         FStar_Syntax_Util.abs bs FStar_Syntax_Syntax.t_unit
                           FStar_Pervasives_Native.None
                          in
                       {
                         FStar_Syntax_Syntax.lbname = (FStar_Util.Inr fv);
                         FStar_Syntax_Syntax.lbunivs = univs1;
                         FStar_Syntax_Syntax.lbtyp = t;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_Tot_lid;
                         FStar_Syntax_Syntax.lbdef = uu____66211;
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
        let uu____66274 =
          FStar_Extraction_ML_UEnv.extend_fv' g1 fv ml_name tysc false false
           in
        match uu____66274 with
        | (g2,mangled_name,exp_binding) ->
            ((let uu____66296 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g2.FStar_Extraction_ML_UEnv.env_tcenv)
                  (FStar_Options.Other "ExtractionReify")
                 in
              if uu____66296
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
        (let uu____66332 =
           FStar_All.pipe_left
             (FStar_TypeChecker_Env.debug
                g.FStar_Extraction_ML_UEnv.env_tcenv)
             (FStar_Options.Other "ExtractionReify")
            in
         if uu____66332
         then
           let uu____66337 = FStar_Syntax_Print.term_to_string tm  in
           FStar_Util.print1 "extract_fv term: %s\n" uu____66337
         else ());
        (let uu____66342 =
           let uu____66343 = FStar_Syntax_Subst.compress tm  in
           uu____66343.FStar_Syntax_Syntax.n  in
         match uu____66342 with
         | FStar_Syntax_Syntax.Tm_uinst (tm1,uu____66351) -> extract_fv tm1
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             let mlp =
               FStar_Extraction_ML_Syntax.mlpath_of_lident
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             let uu____66358 = FStar_Extraction_ML_UEnv.lookup_fv g fv  in
             (match uu____66358 with
              | { FStar_Extraction_ML_UEnv.exp_b_name = uu____66363;
                  FStar_Extraction_ML_UEnv.exp_b_expr = uu____66364;
                  FStar_Extraction_ML_UEnv.exp_b_tscheme = tysc;
                  FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____66366;_} ->
                  let uu____66369 =
                    FStar_All.pipe_left
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.MLTY_Top)
                      (FStar_Extraction_ML_Syntax.MLE_Name mlp)
                     in
                  (uu____66369, tysc))
         | uu____66370 ->
             let uu____66371 =
               let uu____66373 =
                 FStar_Range.string_of_range tm.FStar_Syntax_Syntax.pos  in
               let uu____66375 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.format2 "(%s) Not an fv: %s" uu____66373
                 uu____66375
                in
             failwith uu____66371)
         in
      let extract_action g1 a =
        (let uu____66403 =
           FStar_All.pipe_left
             (FStar_TypeChecker_Env.debug
                g1.FStar_Extraction_ML_UEnv.env_tcenv)
             (FStar_Options.Other "ExtractionReify")
            in
         if uu____66403
         then
           let uu____66408 =
             FStar_Syntax_Print.term_to_string
               a.FStar_Syntax_Syntax.action_typ
              in
           let uu____66410 =
             FStar_Syntax_Print.term_to_string
               a.FStar_Syntax_Syntax.action_defn
              in
           FStar_Util.print2 "Action type %s and term %s\n" uu____66408
             uu____66410
         else ());
        (let uu____66415 = FStar_Extraction_ML_UEnv.action_name ed a  in
         match uu____66415 with
         | (a_nm,a_lid) ->
             let lbname =
               let uu____66435 =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some
                      ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                   FStar_Syntax_Syntax.tun
                  in
               FStar_Util.Inl uu____66435  in
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
             let uu____66465 =
               FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb  in
             (match uu____66465 with
              | (a_let,uu____66481,ty) ->
                  ((let uu____66484 =
                      FStar_All.pipe_left
                        (FStar_TypeChecker_Env.debug
                           g1.FStar_Extraction_ML_UEnv.env_tcenv)
                        (FStar_Options.Other "ExtractionReify")
                       in
                    if uu____66484
                    then
                      let uu____66489 =
                        FStar_Extraction_ML_Code.string_of_mlexpr a_nm a_let
                         in
                      FStar_Util.print1 "Extracted action term: %s\n"
                        uu____66489
                    else ());
                   (let uu____66494 =
                      match a_let.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Let
                          ((uu____66517,mllb::[]),uu____66519) ->
                          (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc
                           with
                           | FStar_Pervasives_Native.Some tysc ->
                               ((mllb.FStar_Extraction_ML_Syntax.mllb_def),
                                 tysc)
                           | FStar_Pervasives_Native.None  ->
                               failwith "No type scheme")
                      | uu____66559 -> failwith "Impossible"  in
                    match uu____66494 with
                    | (exp,tysc) ->
                        ((let uu____66597 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug
                                 g1.FStar_Extraction_ML_UEnv.env_tcenv)
                              (FStar_Options.Other "ExtractionReify")
                             in
                          if uu____66597
                          then
                            ((let uu____66603 =
                                FStar_Extraction_ML_Code.string_of_mlty a_nm
                                  (FStar_Pervasives_Native.snd tysc)
                                 in
                              FStar_Util.print1 "Extracted action type: %s\n"
                                uu____66603);
                             FStar_List.iter
                               (fun x  ->
                                  FStar_Util.print1 "and binders: %s\n" x)
                               (FStar_Pervasives_Native.fst tysc))
                          else ());
                         (let uu____66619 = extend_env g1 a_lid a_nm exp tysc
                             in
                          match uu____66619 with
                          | (env,iface1,impl) -> (env, (iface1, impl))))))))
         in
      let uu____66641 =
        let uu____66648 =
          extract_fv
            (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.return_repr)
           in
        match uu____66648 with
        | (return_tm,ty_sc) ->
            let uu____66665 =
              FStar_Extraction_ML_UEnv.monad_op_name ed "return"  in
            (match uu____66665 with
             | (return_nm,return_lid) ->
                 extend_env g return_lid return_nm return_tm ty_sc)
         in
      match uu____66641 with
      | (g1,return_iface,return_decl) ->
          let uu____66690 =
            let uu____66697 =
              extract_fv
                (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.bind_repr)
               in
            match uu____66697 with
            | (bind_tm,ty_sc) ->
                let uu____66714 =
                  FStar_Extraction_ML_UEnv.monad_op_name ed "bind"  in
                (match uu____66714 with
                 | (bind_nm,bind_lid) ->
                     extend_env g1 bind_lid bind_nm bind_tm ty_sc)
             in
          (match uu____66690 with
           | (g2,bind_iface,bind_decl) ->
               let uu____66739 =
                 FStar_Util.fold_map extract_action g2
                   ed.FStar_Syntax_Syntax.actions
                  in
               (match uu____66739 with
                | (g3,actions) ->
                    let uu____66776 = FStar_List.unzip actions  in
                    (match uu____66776 with
                     | (actions_iface,actions1) ->
                         let uu____66803 =
                           iface_union_l (return_iface :: bind_iface ::
                             actions_iface)
                            in
                         (g3, uu____66803, (return_decl :: bind_decl ::
                           actions1)))))
  
let (extract_sigelt_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle uu____66825 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____66834 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_datacon uu____66851 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) when
          FStar_Extraction_ML_Term.is_arity g t ->
          let uu____66870 =
            extract_type_declaration g lid se.FStar_Syntax_Syntax.sigquals
              se.FStar_Syntax_Syntax.sigattrs univs1 t
             in
          (match uu____66870 with | (env,iface1,uu____66885) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____66891) when
          FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp ->
          let uu____66900 =
            extract_typ_abbrev g se.FStar_Syntax_Syntax.sigquals
              se.FStar_Syntax_Syntax.sigattrs lb
             in
          (match uu____66900 with | (env,iface1,uu____66915) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,_univs,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let uu____66926 =
            (FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption))
              &&
              (let uu____66932 =
                 FStar_TypeChecker_Util.must_erase_for_extraction
                   g.FStar_Extraction_ML_UEnv.env_tcenv t
                  in
               Prims.op_Negation uu____66932)
             in
          if uu____66926
          then
            let uu____66939 =
              let uu____66950 =
                let uu____66951 =
                  let uu____66954 = always_fail lid t  in [uu____66954]  in
                (false, uu____66951)  in
              FStar_Extraction_ML_Term.extract_lb_iface g uu____66950  in
            (match uu____66939 with
             | (g1,bindings) -> (g1, (iface_of_bindings bindings)))
          else (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____66980) ->
          let uu____66985 = FStar_Extraction_ML_Term.extract_lb_iface g lbs
             in
          (match uu____66985 with
           | (g1,bindings) -> (g1, (iface_of_bindings bindings)))
      | FStar_Syntax_Syntax.Sig_main uu____67014 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____67015 ->
          (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_assume uu____67016 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____67023 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____67024 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          (FStar_Syntax_Util.process_pragma p se.FStar_Syntax_Syntax.sigrng;
           (g, empty_iface))
      | FStar_Syntax_Syntax.Sig_splice uu____67039 ->
          failwith "impossible: trying to extract splice"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____67052 =
            (FStar_TypeChecker_Env.is_reifiable_effect
               g.FStar_Extraction_ML_UEnv.env_tcenv
               ed.FStar_Syntax_Syntax.mname)
              && (FStar_List.isEmpty ed.FStar_Syntax_Syntax.binders)
             in
          if uu____67052
          then
            let uu____67065 = extract_reifiable_effect g ed  in
            (match uu____67065 with
             | (env,iface1,uu____67080) -> (env, iface1))
          else (g, empty_iface)
  
let (extract_iface' :
  env_t ->
    FStar_Syntax_Syntax.modul -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun modul  ->
      let uu____67102 = FStar_Options.interactive ()  in
      if uu____67102
      then (g, empty_iface)
      else
        (let uu____67111 = FStar_Options.restore_cmd_line_options true  in
         let decls = modul.FStar_Syntax_Syntax.declarations  in
         let iface1 =
           let uu___1166_67115 = empty_iface  in
           {
             iface_module_name = (g.FStar_Extraction_ML_UEnv.currentModule);
             iface_bindings = (uu___1166_67115.iface_bindings);
             iface_tydefs = (uu___1166_67115.iface_tydefs);
             iface_type_names = (uu___1166_67115.iface_type_names)
           }  in
         let res =
           FStar_List.fold_left
             (fun uu____67133  ->
                fun se  ->
                  match uu____67133 with
                  | (g1,iface2) ->
                      let uu____67145 = extract_sigelt_iface g1 se  in
                      (match uu____67145 with
                       | (g2,iface') ->
                           let uu____67156 = iface_union iface2 iface'  in
                           (g2, uu____67156))) (g, iface1) decls
            in
         (let uu____67158 = FStar_Options.restore_cmd_line_options true  in
          FStar_All.pipe_left (fun a1  -> ()) uu____67158);
         res)
  
let (extract_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.modul -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun modul  ->
      let uu____67175 = FStar_Options.debug_any ()  in
      if uu____67175
      then
        let uu____67182 =
          FStar_Util.format1 "Extracted interface of %s"
            (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
           in
        FStar_Util.measure_execution_time uu____67182
          (fun uu____67190  -> extract_iface' g modul)
      else extract_iface' g modul
  
let (extend_with_iface :
  FStar_Extraction_ML_UEnv.uenv -> iface -> FStar_Extraction_ML_UEnv.uenv) =
  fun g  ->
    fun iface1  ->
      let uu___1184_67204 = g  in
      let uu____67205 =
        let uu____67208 =
          FStar_List.map (fun _67215  -> FStar_Extraction_ML_UEnv.Fv _67215)
            iface1.iface_bindings
           in
        FStar_List.append uu____67208 g.FStar_Extraction_ML_UEnv.env_bindings
         in
      {
        FStar_Extraction_ML_UEnv.env_tcenv =
          (uu___1184_67204.FStar_Extraction_ML_UEnv.env_tcenv);
        FStar_Extraction_ML_UEnv.env_bindings = uu____67205;
        FStar_Extraction_ML_UEnv.tydefs =
          (FStar_List.append iface1.iface_tydefs
             g.FStar_Extraction_ML_UEnv.tydefs);
        FStar_Extraction_ML_UEnv.type_names =
          (FStar_List.append iface1.iface_type_names
             g.FStar_Extraction_ML_UEnv.type_names);
        FStar_Extraction_ML_UEnv.currentModule =
          (uu___1184_67204.FStar_Extraction_ML_UEnv.currentModule)
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
          let uu____67293 =
            FStar_Extraction_ML_Term.term_as_mlty env_iparams ctor.dtyp  in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env_iparams) uu____67293
           in
        let steps =
          [FStar_TypeChecker_Env.Inlining;
          FStar_TypeChecker_Env.UnfoldUntil
            FStar_Syntax_Syntax.delta_constant;
          FStar_TypeChecker_Env.EraseUniverses;
          FStar_TypeChecker_Env.AllowUnboundUniverses]  in
        let names1 =
          let uu____67301 =
            let uu____67302 =
              let uu____67305 =
                FStar_TypeChecker_Normalize.normalize steps
                  env_iparams.FStar_Extraction_ML_UEnv.env_tcenv ctor.dtyp
                 in
              FStar_Syntax_Subst.compress uu____67305  in
            uu____67302.FStar_Syntax_Syntax.n  in
          match uu____67301 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,uu____67310) ->
              FStar_List.map
                (fun uu____67343  ->
                   match uu____67343 with
                   | ({ FStar_Syntax_Syntax.ppname = ppname;
                        FStar_Syntax_Syntax.index = uu____67352;
                        FStar_Syntax_Syntax.sort = uu____67353;_},uu____67354)
                       -> ppname.FStar_Ident.idText) bs
          | uu____67362 -> []  in
        let tys = (ml_tyvars, mlt)  in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp  in
        let uu____67370 =
          FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false  in
        match uu____67370 with
        | (env2,uu____67397,uu____67398) ->
            let uu____67401 =
              let uu____67414 = lident_as_mlsymbol ctor.dname  in
              let uu____67416 =
                let uu____67424 = FStar_Extraction_ML_Util.argTypes mlt  in
                FStar_List.zip names1 uu____67424  in
              (uu____67414, uu____67416)  in
            (env2, uu____67401)
         in
      let extract_one_family env1 ind =
        let uu____67485 = binders_as_mlty_binders env1 ind.iparams  in
        match uu____67485 with
        | (env_iparams,vars) ->
            let uu____67529 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor env_iparams vars) env1)
               in
            (match uu____67529 with
             | (env2,ctors) ->
                 let uu____67636 = FStar_Syntax_Util.arrow_formals ind.ityp
                    in
                 (match uu____67636 with
                  | (indices,uu____67678) ->
                      let ml_params =
                        let uu____67703 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____67729  ->
                                    let uu____67737 =
                                      FStar_Util.string_of_int i  in
                                    Prims.op_Hat "'dummyV" uu____67737))
                           in
                        FStar_List.append vars uu____67703  in
                      let tbody =
                        let uu____67742 =
                          FStar_Util.find_opt
                            (fun uu___619_67747  ->
                               match uu___619_67747 with
                               | FStar_Syntax_Syntax.RecordType uu____67749
                                   -> true
                               | uu____67759 -> false) ind.iquals
                           in
                        match uu____67742 with
                        | FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                            let uu____67771 = FStar_List.hd ctors  in
                            (match uu____67771 with
                             | (uu____67796,c_ty) ->
                                 let fields =
                                   FStar_List.map2
                                     (fun id1  ->
                                        fun uu____67840  ->
                                          match uu____67840 with
                                          | (uu____67851,ty) ->
                                              let lid =
                                                FStar_Ident.lid_of_ids
                                                  (FStar_List.append ns [id1])
                                                 in
                                              let uu____67856 =
                                                lident_as_mlsymbol lid  in
                                              (uu____67856, ty)) ids c_ty
                                    in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____67859 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors
                         in
                      let uu____67862 =
                        let uu____67885 = lident_as_mlsymbol ind.iname  in
                        (false, uu____67885, FStar_Pervasives_Native.None,
                          ml_params, (ind.imetadata),
                          (FStar_Pervasives_Native.Some tbody))
                         in
                      (env2, uu____67862)))
         in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____67930,t,uu____67932,uu____67933,uu____67934);
            FStar_Syntax_Syntax.sigrng = uu____67935;
            FStar_Syntax_Syntax.sigquals = uu____67936;
            FStar_Syntax_Syntax.sigmeta = uu____67937;
            FStar_Syntax_Syntax.sigattrs = uu____67938;_}::[],uu____67939),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____67958 = extract_ctor env [] env { dname = l; dtyp = t }
             in
          (match uu____67958 with
           | (env1,ctor) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____68011),quals) ->
          let uu____68025 =
            bundle_as_inductive_families env ses quals
              se.FStar_Syntax_Syntax.sigattrs
             in
          (match uu____68025 with
           | (env1,ifams) ->
               let uu____68044 =
                 FStar_Util.fold_map extract_one_family env1 ifams  in
               (match uu____68044 with
                | (env2,td) -> (env2, [FStar_Extraction_ML_Syntax.MLM_Ty td])))
      | uu____68153 -> failwith "Unexpected signature element"
  
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
             let uu____68211 = FStar_Syntax_Util.head_and_args t  in
             match uu____68211 with
             | (head1,args) ->
                 let uu____68259 =
                   let uu____68261 =
                     FStar_Syntax_Util.is_fvar FStar_Parser_Const.plugin_attr
                       head1
                      in
                   Prims.op_Negation uu____68261  in
                 if uu____68259
                 then FStar_Pervasives_Native.None
                 else
                   (match args with
                    | ({
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_int (s,uu____68280));
                         FStar_Syntax_Syntax.pos = uu____68281;
                         FStar_Syntax_Syntax.vars = uu____68282;_},uu____68283)::[]
                        ->
                        let uu____68322 =
                          let uu____68326 = FStar_Util.int_of_string s  in
                          FStar_Pervasives_Native.Some uu____68326  in
                        FStar_Pervasives_Native.Some uu____68322
                    | uu____68332 ->
                        FStar_Pervasives_Native.Some
                          FStar_Pervasives_Native.None))
         in
      let uu____68347 =
        let uu____68349 = FStar_Options.codegen ()  in
        uu____68349 <> (FStar_Pervasives_Native.Some FStar_Options.Plugin)
         in
      if uu____68347
      then []
      else
        (let uu____68359 = plugin_with_arity se.FStar_Syntax_Syntax.sigattrs
            in
         match uu____68359 with
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
                      let uu____68401 =
                        let uu____68402 = FStar_Ident.string_of_lid fv_lid1
                           in
                        FStar_Extraction_ML_Syntax.MLC_String uu____68402  in
                      FStar_Extraction_ML_Syntax.MLE_Const uu____68401  in
                    let uu____68404 =
                      FStar_Extraction_ML_Util.interpret_plugin_as_term_fun
                        g.FStar_Extraction_ML_UEnv.env_tcenv fv fv_t
                        arity_opt ml_name_str
                       in
                    match uu____68404 with
                    | FStar_Pervasives_Native.Some
                        (interp,nbe_interp,arity,plugin1) ->
                        let uu____68437 =
                          if plugin1
                          then
                            ("FStar_Tactics_Native.register_plugin",
                              [interp; nbe_interp])
                          else
                            ("FStar_Tactics_Native.register_tactic",
                              [interp])
                           in
                        (match uu____68437 with
                         | (register,args) ->
                             let h =
                               let uu____68474 =
                                 let uu____68475 =
                                   let uu____68476 =
                                     FStar_Ident.lid_of_str register  in
                                   FStar_Extraction_ML_Syntax.mlpath_of_lident
                                     uu____68476
                                    in
                                 FStar_Extraction_ML_Syntax.MLE_Name
                                   uu____68475
                                  in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    FStar_Extraction_ML_Syntax.MLTY_Top)
                                 uu____68474
                                in
                             let arity1 =
                               let uu____68478 =
                                 let uu____68479 =
                                   let uu____68491 =
                                     FStar_Util.string_of_int arity  in
                                   (uu____68491,
                                     FStar_Pervasives_Native.None)
                                    in
                                 FStar_Extraction_ML_Syntax.MLC_Int
                                   uu____68479
                                  in
                               FStar_Extraction_ML_Syntax.MLE_Const
                                 uu____68478
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
              | uu____68520 -> []))
  
let rec (extract_sig :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list))
  =
  fun g  ->
    fun se  ->
      FStar_Extraction_ML_UEnv.debug g
        (fun u  ->
           let uu____68548 = FStar_Syntax_Print.sigelt_to_string se  in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____68548);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle uu____68557 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____68566 ->
           extract_bundle g se
       | FStar_Syntax_Syntax.Sig_datacon uu____68583 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           FStar_TypeChecker_Env.is_reifiable_effect
             g.FStar_Extraction_ML_UEnv.env_tcenv
             ed.FStar_Syntax_Syntax.mname
           ->
           let uu____68600 = extract_reifiable_effect g ed  in
           (match uu____68600 with | (env,_iface,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_splice uu____68624 ->
           failwith "impossible: trying to extract splice"
       | FStar_Syntax_Syntax.Sig_new_effect uu____68638 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let uu____68644 =
             extract_type_declaration g lid se.FStar_Syntax_Syntax.sigquals
               se.FStar_Syntax_Syntax.sigattrs univs1 t
              in
           (match uu____68644 with | (env,uu____68660,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____68669) when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let uu____68678 =
             extract_typ_abbrev g se.FStar_Syntax_Syntax.sigquals
               se.FStar_Syntax_Syntax.sigattrs lb
              in
           (match uu____68678 with | (env,uu____68694,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____68703) ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____68714 =
             let uu____68723 =
               FStar_Syntax_Util.extract_attr'
                 FStar_Parser_Const.postprocess_extr_with attrs
                in
             match uu____68723 with
             | FStar_Pervasives_Native.None  ->
                 (attrs, FStar_Pervasives_Native.None)
             | FStar_Pervasives_Native.Some
                 (ats,(tau,FStar_Pervasives_Native.None )::uu____68752) ->
                 (ats, (FStar_Pervasives_Native.Some tau))
             | FStar_Pervasives_Native.Some (ats,args) ->
                 (FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng
                    (FStar_Errors.Warning_UnrecognizedAttribute,
                      "Ill-formed application of `postprocess_for_extraction_with`");
                  (attrs, FStar_Pervasives_Native.None))
              in
           (match uu____68714 with
            | (attrs1,post_tau) ->
                let postprocess_lb tau lb =
                  let lbdef =
                    FStar_TypeChecker_Env.postprocess
                      g.FStar_Extraction_ML_UEnv.env_tcenv tau
                      lb.FStar_Syntax_Syntax.lbtyp
                      lb.FStar_Syntax_Syntax.lbdef
                     in
                  let uu___1403_68838 = lb  in
                  {
                    FStar_Syntax_Syntax.lbname =
                      (uu___1403_68838.FStar_Syntax_Syntax.lbname);
                    FStar_Syntax_Syntax.lbunivs =
                      (uu___1403_68838.FStar_Syntax_Syntax.lbunivs);
                    FStar_Syntax_Syntax.lbtyp =
                      (uu___1403_68838.FStar_Syntax_Syntax.lbtyp);
                    FStar_Syntax_Syntax.lbeff =
                      (uu___1403_68838.FStar_Syntax_Syntax.lbeff);
                    FStar_Syntax_Syntax.lbdef = lbdef;
                    FStar_Syntax_Syntax.lbattrs =
                      (uu___1403_68838.FStar_Syntax_Syntax.lbattrs);
                    FStar_Syntax_Syntax.lbpos =
                      (uu___1403_68838.FStar_Syntax_Syntax.lbpos)
                  }  in
                let lbs1 =
                  let uu____68847 =
                    match post_tau with
                    | FStar_Pervasives_Native.Some tau ->
                        FStar_List.map (postprocess_lb tau)
                          (FStar_Pervasives_Native.snd lbs)
                    | FStar_Pervasives_Native.None  ->
                        FStar_Pervasives_Native.snd lbs
                     in
                  ((FStar_Pervasives_Native.fst lbs), uu____68847)  in
                let uu____68865 =
                  let uu____68872 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_let
                         (lbs1, FStar_Syntax_Util.exp_false_bool))
                      FStar_Pervasives_Native.None
                      se.FStar_Syntax_Syntax.sigrng
                     in
                  FStar_Extraction_ML_Term.term_as_mlexpr g uu____68872  in
                (match uu____68865 with
                 | (ml_let,uu____68889,uu____68890) ->
                     (match ml_let.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Let
                          ((flavor,bindings),uu____68899) ->
                          let flags = FStar_List.choose flag_of_qual quals
                             in
                          let flags' = extract_metadata attrs1  in
                          let uu____68916 =
                            FStar_List.fold_left2
                              (fun uu____68942  ->
                                 fun ml_lb  ->
                                   fun uu____68944  ->
                                     match (uu____68942, uu____68944) with
                                     | ((env,ml_lbs),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbname;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uu____68966;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = t;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____68968;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = uu____68969;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____68970;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____68971;_})
                                         ->
                                         let uu____68996 =
                                           FStar_All.pipe_right
                                             ml_lb.FStar_Extraction_ML_Syntax.mllb_meta
                                             (FStar_List.contains
                                                FStar_Extraction_ML_Syntax.Erased)
                                            in
                                         if uu____68996
                                         then (env, ml_lbs)
                                         else
                                           (let lb_lid =
                                              let uu____69013 =
                                                let uu____69016 =
                                                  FStar_Util.right lbname  in
                                                uu____69016.FStar_Syntax_Syntax.fv_name
                                                 in
                                              uu____69013.FStar_Syntax_Syntax.v
                                               in
                                            let flags'' =
                                              let uu____69020 =
                                                let uu____69021 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____69021.FStar_Syntax_Syntax.n
                                                 in
                                              match uu____69020 with
                                              | FStar_Syntax_Syntax.Tm_arrow
                                                  (uu____69026,{
                                                                 FStar_Syntax_Syntax.n
                                                                   =
                                                                   FStar_Syntax_Syntax.Comp
                                                                   {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____69027;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    = e;
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    =
                                                                    uu____69029;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____69030;
                                                                    FStar_Syntax_Syntax.flags
                                                                    =
                                                                    uu____69031;_};
                                                                 FStar_Syntax_Syntax.pos
                                                                   =
                                                                   uu____69032;
                                                                 FStar_Syntax_Syntax.vars
                                                                   =
                                                                   uu____69033;_})
                                                  when
                                                  let uu____69068 =
                                                    FStar_Ident.string_of_lid
                                                      e
                                                     in
                                                  uu____69068 =
                                                    "FStar.HyperStack.ST.StackInline"
                                                  ->
                                                  [FStar_Extraction_ML_Syntax.StackInline]
                                              | uu____69072 -> []  in
                                            let meta =
                                              FStar_List.append flags
                                                (FStar_List.append flags'
                                                   flags'')
                                               in
                                            let ml_lb1 =
                                              let uu___1451_69077 = ml_lb  in
                                              {
                                                FStar_Extraction_ML_Syntax.mllb_name
                                                  =
                                                  (uu___1451_69077.FStar_Extraction_ML_Syntax.mllb_name);
                                                FStar_Extraction_ML_Syntax.mllb_tysc
                                                  =
                                                  (uu___1451_69077.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                FStar_Extraction_ML_Syntax.mllb_add_unit
                                                  =
                                                  (uu___1451_69077.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                FStar_Extraction_ML_Syntax.mllb_def
                                                  =
                                                  (uu___1451_69077.FStar_Extraction_ML_Syntax.mllb_def);
                                                FStar_Extraction_ML_Syntax.mllb_meta
                                                  = meta;
                                                FStar_Extraction_ML_Syntax.print_typ
                                                  =
                                                  (uu___1451_69077.FStar_Extraction_ML_Syntax.print_typ)
                                              }  in
                                            let uu____69078 =
                                              let uu____69083 =
                                                FStar_All.pipe_right quals
                                                  (FStar_Util.for_some
                                                     (fun uu___620_69090  ->
                                                        match uu___620_69090
                                                        with
                                                        | FStar_Syntax_Syntax.Projector
                                                            uu____69092 ->
                                                            true
                                                        | uu____69098 ->
                                                            false))
                                                 in
                                              if uu____69083
                                              then
                                                let mname =
                                                  let uu____69114 =
                                                    mangle_projector_lid
                                                      lb_lid
                                                     in
                                                  FStar_All.pipe_right
                                                    uu____69114
                                                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                                                   in
                                                let uu____69123 =
                                                  let uu____69131 =
                                                    FStar_Util.right lbname
                                                     in
                                                  let uu____69132 =
                                                    FStar_Util.must
                                                      ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc
                                                     in
                                                  FStar_Extraction_ML_UEnv.extend_fv'
                                                    env uu____69131 mname
                                                    uu____69132
                                                    ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                                    false
                                                   in
                                                match uu____69123 with
                                                | (env1,uu____69139,uu____69140)
                                                    ->
                                                    (env1,
                                                      (let uu___1464_69144 =
                                                         ml_lb1  in
                                                       {
                                                         FStar_Extraction_ML_Syntax.mllb_name
                                                           =
                                                           (FStar_Pervasives_Native.snd
                                                              mname);
                                                         FStar_Extraction_ML_Syntax.mllb_tysc
                                                           =
                                                           (uu___1464_69144.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                         FStar_Extraction_ML_Syntax.mllb_add_unit
                                                           =
                                                           (uu___1464_69144.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                         FStar_Extraction_ML_Syntax.mllb_def
                                                           =
                                                           (uu___1464_69144.FStar_Extraction_ML_Syntax.mllb_def);
                                                         FStar_Extraction_ML_Syntax.mllb_meta
                                                           =
                                                           (uu___1464_69144.FStar_Extraction_ML_Syntax.mllb_meta);
                                                         FStar_Extraction_ML_Syntax.print_typ
                                                           =
                                                           (uu___1464_69144.FStar_Extraction_ML_Syntax.print_typ)
                                                       }))
                                              else
                                                (let uu____69151 =
                                                   let uu____69159 =
                                                     FStar_Util.must
                                                       ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc
                                                      in
                                                   FStar_Extraction_ML_UEnv.extend_lb
                                                     env lbname t uu____69159
                                                     ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                                     false
                                                    in
                                                 match uu____69151 with
                                                 | (env1,uu____69166,uu____69167)
                                                     -> (env1, ml_lb1))
                                               in
                                            match uu____69078 with
                                            | (g1,ml_lb2) ->
                                                (g1, (ml_lb2 :: ml_lbs))))
                              (g, []) bindings
                              (FStar_Pervasives_Native.snd lbs1)
                             in
                          (match uu____68916 with
                           | (g1,ml_lbs') ->
                               let uu____69197 =
                                 let uu____69200 =
                                   let uu____69203 =
                                     let uu____69204 =
                                       FStar_Extraction_ML_Util.mlloc_of_range
                                         se.FStar_Syntax_Syntax.sigrng
                                        in
                                     FStar_Extraction_ML_Syntax.MLM_Loc
                                       uu____69204
                                      in
                                   [uu____69203;
                                   FStar_Extraction_ML_Syntax.MLM_Let
                                     (flavor, (FStar_List.rev ml_lbs'))]
                                    in
                                 let uu____69207 =
                                   maybe_register_plugin g1 se  in
                                 FStar_List.append uu____69200 uu____69207
                                  in
                               (g1, uu____69197))
                      | uu____69212 ->
                          let uu____69213 =
                            let uu____69215 =
                              FStar_Extraction_ML_Code.string_of_mlexpr
                                g.FStar_Extraction_ML_UEnv.currentModule
                                ml_let
                               in
                            FStar_Util.format1
                              "Impossible: Translated a let to a non-let: %s"
                              uu____69215
                             in
                          failwith uu____69213)))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____69225,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____69230 =
             (FStar_All.pipe_right quals
                (FStar_List.contains FStar_Syntax_Syntax.Assumption))
               &&
               (let uu____69236 =
                  FStar_TypeChecker_Util.must_erase_for_extraction
                    g.FStar_Extraction_ML_UEnv.env_tcenv t
                   in
                Prims.op_Negation uu____69236)
              in
           if uu____69230
           then
             let always_fail1 =
               let uu___1484_69246 = se  in
               let uu____69247 =
                 let uu____69248 =
                   let uu____69255 =
                     let uu____69256 =
                       let uu____69259 = always_fail lid t  in [uu____69259]
                        in
                     (false, uu____69256)  in
                   (uu____69255, [])  in
                 FStar_Syntax_Syntax.Sig_let uu____69248  in
               {
                 FStar_Syntax_Syntax.sigel = uu____69247;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___1484_69246.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___1484_69246.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___1484_69246.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___1484_69246.FStar_Syntax_Syntax.sigattrs)
               }  in
             let uu____69266 = extract_sig g always_fail1  in
             (match uu____69266 with
              | (g1,mlm) ->
                  let uu____69285 =
                    FStar_Util.find_map quals
                      (fun uu___621_69290  ->
                         match uu___621_69290 with
                         | FStar_Syntax_Syntax.Discriminator l ->
                             FStar_Pervasives_Native.Some l
                         | uu____69294 -> FStar_Pervasives_Native.None)
                     in
                  (match uu____69285 with
                   | FStar_Pervasives_Native.Some l ->
                       let uu____69302 =
                         let uu____69305 =
                           let uu____69306 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng
                              in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____69306  in
                         let uu____69307 =
                           let uu____69310 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l
                              in
                           [uu____69310]  in
                         uu____69305 :: uu____69307  in
                       (g1, uu____69302)
                   | uu____69313 ->
                       let uu____69316 =
                         FStar_Util.find_map quals
                           (fun uu___622_69322  ->
                              match uu___622_69322 with
                              | FStar_Syntax_Syntax.Projector (l,uu____69326)
                                  -> FStar_Pervasives_Native.Some l
                              | uu____69327 -> FStar_Pervasives_Native.None)
                          in
                       (match uu____69316 with
                        | FStar_Pervasives_Native.Some uu____69334 ->
                            (g1, [])
                        | uu____69337 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____69347 = FStar_Extraction_ML_Term.term_as_mlexpr g e  in
           (match uu____69347 with
            | (ml_main,uu____69361,uu____69362) ->
                let uu____69363 =
                  let uu____69366 =
                    let uu____69367 =
                      FStar_Extraction_ML_Util.mlloc_of_range
                        se.FStar_Syntax_Syntax.sigrng
                       in
                    FStar_Extraction_ML_Syntax.MLM_Loc uu____69367  in
                  [uu____69366; FStar_Extraction_ML_Syntax.MLM_Top ml_main]
                   in
                (g, uu____69363))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____69370 ->
           failwith "impossible -- removed by tc.fs"
       | FStar_Syntax_Syntax.Sig_assume uu____69378 -> (g, [])
       | FStar_Syntax_Syntax.Sig_sub_effect uu____69387 -> (g, [])
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____69390 -> (g, [])
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
      let uu____69432 = FStar_Options.restore_cmd_line_options true  in
      let name =
        FStar_Extraction_ML_Syntax.mlpath_of_lident
          m.FStar_Syntax_Syntax.name
         in
      let g1 =
        let uu___1527_69436 = g  in
        let uu____69437 =
          FStar_TypeChecker_Env.set_current_module
            g.FStar_Extraction_ML_UEnv.env_tcenv m.FStar_Syntax_Syntax.name
           in
        {
          FStar_Extraction_ML_UEnv.env_tcenv = uu____69437;
          FStar_Extraction_ML_UEnv.env_bindings =
            (uu___1527_69436.FStar_Extraction_ML_UEnv.env_bindings);
          FStar_Extraction_ML_UEnv.tydefs =
            (uu___1527_69436.FStar_Extraction_ML_UEnv.tydefs);
          FStar_Extraction_ML_UEnv.type_names =
            (uu___1527_69436.FStar_Extraction_ML_UEnv.type_names);
          FStar_Extraction_ML_UEnv.currentModule = name
        }  in
      let uu____69438 =
        FStar_Util.fold_map
          (fun g2  ->
             fun se  ->
               let uu____69457 =
                 FStar_Options.debug_module
                   (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                  in
               if uu____69457
               then
                 let nm =
                   let uu____69468 =
                     FStar_All.pipe_right
                       (FStar_Syntax_Util.lids_of_sigelt se)
                       (FStar_List.map FStar_Ident.string_of_lid)
                      in
                   FStar_All.pipe_right uu____69468
                     (FStar_String.concat ", ")
                    in
                 (FStar_Util.print1 "+++About to extract {%s}\n" nm;
                  (let uu____69485 =
                     FStar_Util.format1 "---Extracted {%s}" nm  in
                   FStar_Util.measure_execution_time uu____69485
                     (fun uu____69495  -> extract_sig g2 se)))
               else extract_sig g2 se) g1 m.FStar_Syntax_Syntax.declarations
         in
      match uu____69438 with
      | (g2,sigs) ->
          let mlm = FStar_List.flatten sigs  in
          let is_kremlin =
            let uu____69517 = FStar_Options.codegen ()  in
            uu____69517 =
              (FStar_Pervasives_Native.Some FStar_Options.Kremlin)
             in
          if
            ((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims") &&
              (is_kremlin ||
                 (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface))
          then
            ((let uu____69532 =
                let uu____69534 = FStar_Options.silent ()  in
                Prims.op_Negation uu____69534  in
              if uu____69532
              then
                let uu____69537 =
                  FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
                FStar_Util.print1 "Extracted module %s\n" uu____69537
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
      (let uu____69612 = FStar_Options.restore_cmd_line_options true  in
       FStar_All.pipe_left (fun a2  -> ()) uu____69612);
      (let uu____69615 =
         let uu____69617 =
           FStar_Options.should_extract
             (m.FStar_Syntax_Syntax.name).FStar_Ident.str
            in
         Prims.op_Negation uu____69617  in
       if uu____69615
       then
         let uu____69620 =
           let uu____69622 =
             FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
           FStar_Util.format1
             "Extract called on a module %s that should not be extracted"
             uu____69622
            in
         failwith uu____69620
       else ());
      (let uu____69627 = FStar_Options.interactive ()  in
       if uu____69627
       then (g, FStar_Pervasives_Native.None)
       else
         (let res =
            let uu____69647 = FStar_Options.debug_any ()  in
            if uu____69647
            then
              let msg =
                let uu____69658 =
                  FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name
                   in
                FStar_Util.format1 "Extracting module %s\n" uu____69658  in
              FStar_Util.measure_execution_time msg
                (fun uu____69668  -> extract' g m)
            else extract' g m  in
          (let uu____69672 = FStar_Options.restore_cmd_line_options true  in
           FStar_All.pipe_left (fun a3  -> ()) uu____69672);
          res))
  
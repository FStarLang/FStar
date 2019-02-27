open Prims
type env_t = FStar_Extraction_ML_UEnv.uenv
let (fail_exp :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun lid  ->
    fun t  ->
      let uu____68681 =
        let uu____68688 =
          let uu____68689 =
            let uu____68706 =
              FStar_Syntax_Syntax.fvar FStar_Parser_Const.failwith_lid
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            let uu____68709 =
              let uu____68720 = FStar_Syntax_Syntax.iarg t  in
              let uu____68729 =
                let uu____68740 =
                  let uu____68749 =
                    let uu____68750 =
                      let uu____68757 =
                        let uu____68758 =
                          let uu____68759 =
                            let uu____68765 =
                              let uu____68767 =
                                FStar_Syntax_Print.lid_to_string lid  in
                              Prims.op_Hat "Not yet implemented:" uu____68767
                               in
                            (uu____68765, FStar_Range.dummyRange)  in
                          FStar_Const.Const_string uu____68759  in
                        FStar_Syntax_Syntax.Tm_constant uu____68758  in
                      FStar_Syntax_Syntax.mk uu____68757  in
                    uu____68750 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange
                     in
                  FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____68749
                   in
                [uu____68740]  in
              uu____68720 :: uu____68729  in
            (uu____68706, uu____68709)  in
          FStar_Syntax_Syntax.Tm_app uu____68689  in
        FStar_Syntax_Syntax.mk uu____68688  in
      uu____68681 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (always_fail :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.letbinding)
  =
  fun lid  ->
    fun t  ->
      let imp =
        let uu____68839 = FStar_Syntax_Util.arrow_formals t  in
        match uu____68839 with
        | ([],t1) ->
            let b =
              let uu____68882 =
                FStar_Syntax_Syntax.gen_bv "_" FStar_Pervasives_Native.None
                  t1
                 in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____68882
               in
            let uu____68890 = fail_exp lid t1  in
            FStar_Syntax_Util.abs [b] uu____68890
              FStar_Pervasives_Native.None
        | (bs,t1) ->
            let uu____68927 = fail_exp lid t1  in
            FStar_Syntax_Util.abs bs uu____68927 FStar_Pervasives_Native.None
         in
      let lb =
        let uu____68931 =
          let uu____68936 =
            FStar_Syntax_Syntax.lid_as_fv lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Util.Inr uu____68936  in
        {
          FStar_Syntax_Syntax.lbname = uu____68931;
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
  'Auu____68958 . 'Auu____68958 Prims.list -> ('Auu____68958 * 'Auu____68958)
  =
  fun uu___612_68969  ->
    match uu___612_68969 with
    | a::b::[] -> (a, b)
    | uu____68974 -> failwith "Expected a list with 2 elements"
  
let (flag_of_qual :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option)
  =
  fun uu___613_68989  ->
    match uu___613_68989 with
    | FStar_Syntax_Syntax.Assumption  ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Assumed
    | FStar_Syntax_Syntax.Private  ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Private
    | FStar_Syntax_Syntax.NoExtract  ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.NoExtract
    | uu____68992 -> FStar_Pervasives_Native.None
  
let rec (extract_meta :
  FStar_Syntax_Syntax.term ->
    FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option)
  =
  fun x  ->
    let uu____69001 = FStar_Syntax_Subst.compress x  in
    match uu____69001 with
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
        FStar_Syntax_Syntax.pos = uu____69005;
        FStar_Syntax_Syntax.vars = uu____69006;_} ->
        let uu____69009 =
          let uu____69011 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____69011  in
        (match uu____69009 with
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
         | uu____69020 -> FStar_Pervasives_Native.None)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____69023;
             FStar_Syntax_Syntax.vars = uu____69024;_},({
                                                          FStar_Syntax_Syntax.n
                                                            =
                                                            FStar_Syntax_Syntax.Tm_constant
                                                            (FStar_Const.Const_string
                                                            (s,uu____69026));
                                                          FStar_Syntax_Syntax.pos
                                                            = uu____69027;
                                                          FStar_Syntax_Syntax.vars
                                                            = uu____69028;_},uu____69029)::[]);
        FStar_Syntax_Syntax.pos = uu____69030;
        FStar_Syntax_Syntax.vars = uu____69031;_} ->
        let uu____69074 =
          let uu____69076 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____69076  in
        (match uu____69074 with
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
         | uu____69085 -> FStar_Pervasives_Native.None)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("KremlinPrivate",uu____69087));
        FStar_Syntax_Syntax.pos = uu____69088;
        FStar_Syntax_Syntax.vars = uu____69089;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Private
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("c_inline",uu____69094));
        FStar_Syntax_Syntax.pos = uu____69095;
        FStar_Syntax_Syntax.vars = uu____69096;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.CInline
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("substitute",uu____69101));
        FStar_Syntax_Syntax.pos = uu____69102;
        FStar_Syntax_Syntax.vars = uu____69103;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Substitute
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_meta (x1,uu____69109);
        FStar_Syntax_Syntax.pos = uu____69110;
        FStar_Syntax_Syntax.vars = uu____69111;_} -> extract_meta x1
    | uu____69118 -> FStar_Pervasives_Native.None
  
let (extract_metadata :
  FStar_Syntax_Syntax.term Prims.list ->
    FStar_Extraction_ML_Syntax.meta Prims.list)
  = fun metas  -> FStar_List.choose extract_meta metas 
let binders_as_mlty_binders :
  'Auu____69138 .
    FStar_Extraction_ML_UEnv.uenv ->
      (FStar_Syntax_Syntax.bv * 'Auu____69138) Prims.list ->
        (FStar_Extraction_ML_UEnv.uenv * Prims.string Prims.list)
  =
  fun env  ->
    fun bs  ->
      FStar_Util.fold_map
        (fun env1  ->
           fun uu____69180  ->
             match uu____69180 with
             | (bv,uu____69191) ->
                 let uu____69192 =
                   let uu____69193 =
                     let uu____69196 =
                       let uu____69197 =
                         FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv  in
                       FStar_Extraction_ML_Syntax.MLTY_Var uu____69197  in
                     FStar_Pervasives_Native.Some uu____69196  in
                   FStar_Extraction_ML_UEnv.extend_ty env1 bv uu____69193  in
                 let uu____69199 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv
                    in
                 (uu____69192, uu____69199)) env bs
  
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
    let uu____69400 = FStar_Syntax_Print.lid_to_string i.iname  in
    let uu____69402 = FStar_Syntax_Print.binders_to_string " " i.iparams  in
    let uu____69405 = FStar_Syntax_Print.term_to_string i.ityp  in
    let uu____69407 =
      let uu____69409 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d  ->
                let uu____69423 = FStar_Syntax_Print.lid_to_string d.dname
                   in
                let uu____69425 =
                  let uu____69427 = FStar_Syntax_Print.term_to_string d.dtyp
                     in
                  Prims.op_Hat " : " uu____69427  in
                Prims.op_Hat uu____69423 uu____69425))
         in
      FStar_All.pipe_right uu____69409 (FStar_String.concat "\n\t\t")  in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____69400 uu____69402
      uu____69405 uu____69407
  
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
          let uu____69481 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun se  ->
                   match se.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,_us,bs,t,_mut_i,datas) ->
                       let uu____69529 = FStar_Syntax_Subst.open_term bs t
                          in
                       (match uu____69529 with
                        | (bs1,t1) ->
                            let datas1 =
                              FStar_All.pipe_right ses
                                (FStar_List.collect
                                   (fun se1  ->
                                      match se1.FStar_Syntax_Syntax.sigel
                                      with
                                      | FStar_Syntax_Syntax.Sig_datacon
                                          (d,uu____69568,t2,l',nparams,uu____69572)
                                          when FStar_Ident.lid_equals l l' ->
                                          let uu____69579 =
                                            FStar_Syntax_Util.arrow_formals
                                              t2
                                             in
                                          (match uu____69579 with
                                           | (bs',body) ->
                                               let uu____69618 =
                                                 FStar_Util.first_N
                                                   (FStar_List.length bs1)
                                                   bs'
                                                  in
                                               (match uu____69618 with
                                                | (bs_params,rest) ->
                                                    let subst1 =
                                                      FStar_List.map2
                                                        (fun uu____69709  ->
                                                           fun uu____69710 
                                                             ->
                                                             match (uu____69709,
                                                                    uu____69710)
                                                             with
                                                             | ((b',uu____69736),
                                                                (b,uu____69738))
                                                                 ->
                                                                 let uu____69759
                                                                   =
                                                                   let uu____69766
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    b  in
                                                                   (b',
                                                                    uu____69766)
                                                                    in
                                                                 FStar_Syntax_Syntax.NT
                                                                   uu____69759)
                                                        bs_params bs1
                                                       in
                                                    let t3 =
                                                      let uu____69772 =
                                                        let uu____69773 =
                                                          FStar_Syntax_Syntax.mk_Total
                                                            body
                                                           in
                                                        FStar_Syntax_Util.arrow
                                                          rest uu____69773
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____69772
                                                        (FStar_Syntax_Subst.subst
                                                           subst1)
                                                       in
                                                    [{ dname = d; dtyp = t3 }]))
                                      | uu____69776 -> []))
                               in
                            let metadata =
                              let uu____69780 =
                                extract_metadata
                                  (FStar_List.append
                                     se.FStar_Syntax_Syntax.sigattrs attrs)
                                 in
                              let uu____69783 =
                                FStar_List.choose flag_of_qual quals  in
                              FStar_List.append uu____69780 uu____69783  in
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
                   | uu____69790 -> (env1, [])) env ses
             in
          match uu____69481 with
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
    let uu___819_69970 = empty_iface  in
    {
      iface_module_name = (uu___819_69970.iface_module_name);
      iface_bindings = fvs;
      iface_tydefs = (uu___819_69970.iface_tydefs);
      iface_type_names = (uu___819_69970.iface_type_names)
    }
  
let (iface_of_tydefs : FStar_Extraction_ML_UEnv.tydef Prims.list -> iface) =
  fun tds  ->
    let uu___822_69981 = empty_iface  in
    let uu____69982 =
      FStar_List.map (fun td  -> td.FStar_Extraction_ML_UEnv.tydef_fv) tds
       in
    {
      iface_module_name = (uu___822_69981.iface_module_name);
      iface_bindings = (uu___822_69981.iface_bindings);
      iface_tydefs = tds;
      iface_type_names = uu____69982
    }
  
let (iface_of_type_names : FStar_Syntax_Syntax.fv Prims.list -> iface) =
  fun fvs  ->
    let uu___826_69997 = empty_iface  in
    {
      iface_module_name = (uu___826_69997.iface_module_name);
      iface_bindings = (uu___826_69997.iface_bindings);
      iface_tydefs = (uu___826_69997.iface_tydefs);
      iface_type_names = fvs
    }
  
let (iface_union : iface -> iface -> iface) =
  fun if1  ->
    fun if2  ->
      let uu____70009 =
        if if1.iface_module_name <> if1.iface_module_name
        then failwith "Union not defined"
        else if1.iface_module_name  in
      {
        iface_module_name = uu____70009;
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
  'Auu____70054 .
    FStar_Extraction_ML_Syntax.mlpath ->
      ('Auu____70054 * FStar_Extraction_ML_Syntax.mlty) -> Prims.string
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
      let uu____70086 =
        FStar_Extraction_ML_Code.string_of_mlexpr cm
          e.FStar_Extraction_ML_UEnv.exp_b_expr
         in
      let uu____70088 =
        tscheme_to_string cm e.FStar_Extraction_ML_UEnv.exp_b_tscheme  in
      let uu____70090 =
        FStar_Util.string_of_bool e.FStar_Extraction_ML_UEnv.exp_b_inst_ok
         in
      FStar_Util.format4
        "{\n\texp_b_name = %s\n\texp_b_expr = %s\n\texp_b_tscheme = %s\n\texp_b_is_rec = %s }"
        e.FStar_Extraction_ML_UEnv.exp_b_name uu____70086 uu____70088
        uu____70090
  
let (print_binding :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_UEnv.exp_binding) ->
      Prims.string)
  =
  fun cm  ->
    fun uu____70108  ->
      match uu____70108 with
      | (fv,exp_binding) ->
          let uu____70116 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____70118 = print_exp_binding cm exp_binding  in
          FStar_Util.format2 "(%s, %s)" uu____70116 uu____70118
  
let (print_tydef :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_UEnv.tydef -> Prims.string)
  =
  fun cm  ->
    fun tydef  ->
      let uu____70133 =
        FStar_Syntax_Print.fv_to_string
          tydef.FStar_Extraction_ML_UEnv.tydef_fv
         in
      let uu____70135 =
        tscheme_to_string cm tydef.FStar_Extraction_ML_UEnv.tydef_def  in
      FStar_Util.format2 "(%s, %s)" uu____70133 uu____70135
  
let (iface_to_string : iface -> Prims.string) =
  fun iface1  ->
    let cm = iface1.iface_module_name  in
    let print_type_name tn = FStar_Syntax_Print.fv_to_string tn  in
    let uu____70153 =
      let uu____70155 =
        FStar_List.map (print_binding cm) iface1.iface_bindings  in
      FStar_All.pipe_right uu____70155 (FStar_String.concat "\n")  in
    let uu____70169 =
      let uu____70171 = FStar_List.map (print_tydef cm) iface1.iface_tydefs
         in
      FStar_All.pipe_right uu____70171 (FStar_String.concat "\n")  in
    let uu____70181 =
      let uu____70183 =
        FStar_List.map print_type_name iface1.iface_type_names  in
      FStar_All.pipe_right uu____70183 (FStar_String.concat "\n")  in
    FStar_Util.format4
      "Interface %s = {\niface_bindings=\n%s;\n\niface_tydefs=\n%s;\n\niface_type_names=%s;\n}"
      (mlpath_to_string iface1.iface_module_name) uu____70153 uu____70169
      uu____70181
  
let (gamma_to_string : FStar_Extraction_ML_UEnv.uenv -> Prims.string) =
  fun env  ->
    let cm = env.FStar_Extraction_ML_UEnv.currentModule  in
    let gamma =
      FStar_List.collect
        (fun uu___614_70216  ->
           match uu___614_70216 with
           | FStar_Extraction_ML_UEnv.Fv (b,e) -> [(b, e)]
           | uu____70233 -> []) env.FStar_Extraction_ML_UEnv.env_bindings
       in
    let uu____70238 =
      let uu____70240 = FStar_List.map (print_binding cm) gamma  in
      FStar_All.pipe_right uu____70240 (FStar_String.concat "\n")  in
    FStar_Util.format1 "Gamma = {\n %s }" uu____70238
  
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
          let uu____70300 =
            let uu____70309 =
              FStar_TypeChecker_Env.open_universes_in
                env.FStar_Extraction_ML_UEnv.env_tcenv
                lb.FStar_Syntax_Syntax.lbunivs
                [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp]
               in
            match uu____70309 with
            | (tcenv,uu____70327,def_typ) ->
                let uu____70333 = as_pair def_typ  in (tcenv, uu____70333)
             in
          match uu____70300 with
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
                let uu____70364 =
                  let uu____70365 = FStar_Syntax_Subst.compress lbdef1  in
                  FStar_All.pipe_right uu____70365 FStar_Syntax_Util.unmeta
                   in
                FStar_All.pipe_right uu____70364 FStar_Syntax_Util.un_uinst
                 in
              let def1 =
                match def.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_abs uu____70373 ->
                    FStar_Extraction_ML_Term.normalize_abs def
                | uu____70392 -> def  in
              let uu____70393 =
                match def1.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____70404) ->
                    FStar_Syntax_Subst.open_term bs body
                | uu____70429 -> ([], def1)  in
              (match uu____70393 with
               | (bs,body) ->
                   let assumed =
                     FStar_Util.for_some
                       (fun uu___615_70449  ->
                          match uu___615_70449 with
                          | FStar_Syntax_Syntax.Assumption  -> true
                          | uu____70452 -> false) quals
                      in
                   let uu____70454 = binders_as_mlty_binders env bs  in
                   (match uu____70454 with
                    | (env1,ml_bs) ->
                        let body1 =
                          let uu____70481 =
                            FStar_Extraction_ML_Term.term_as_mlty env1 body
                             in
                          FStar_All.pipe_right uu____70481
                            (FStar_Extraction_ML_Util.eraseTypeDeep
                               (FStar_Extraction_ML_Util.udelta_unfold env1))
                           in
                        let mangled_projector =
                          let uu____70486 =
                            FStar_All.pipe_right quals
                              (FStar_Util.for_some
                                 (fun uu___616_70493  ->
                                    match uu___616_70493 with
                                    | FStar_Syntax_Syntax.Projector
                                        uu____70495 -> true
                                    | uu____70501 -> false))
                             in
                          if uu____70486
                          then
                            let mname = mangle_projector_lid lid  in
                            FStar_Pervasives_Native.Some
                              ((mname.FStar_Ident.ident).FStar_Ident.idText)
                          else FStar_Pervasives_Native.None  in
                        let metadata =
                          let uu____70515 = extract_metadata attrs  in
                          let uu____70518 =
                            FStar_List.choose flag_of_qual quals  in
                          FStar_List.append uu____70515 uu____70518  in
                        let td =
                          let uu____70541 = lident_as_mlsymbol lid  in
                          (assumed, uu____70541, mangled_projector, ml_bs,
                            metadata,
                            (FStar_Pervasives_Native.Some
                               (FStar_Extraction_ML_Syntax.MLTD_Abbrev body1)))
                           in
                        let def2 =
                          let uu____70553 =
                            let uu____70554 =
                              let uu____70555 = FStar_Ident.range_of_lid lid
                                 in
                              FStar_Extraction_ML_Util.mlloc_of_range
                                uu____70555
                               in
                            FStar_Extraction_ML_Syntax.MLM_Loc uu____70554
                             in
                          [uu____70553;
                          FStar_Extraction_ML_Syntax.MLM_Ty [td]]  in
                        let uu____70556 =
                          let uu____70561 =
                            FStar_All.pipe_right quals
                              (FStar_Util.for_some
                                 (fun uu___617_70567  ->
                                    match uu___617_70567 with
                                    | FStar_Syntax_Syntax.Assumption  -> true
                                    | FStar_Syntax_Syntax.New  -> true
                                    | uu____70571 -> false))
                             in
                          if uu____70561
                          then
                            let uu____70578 =
                              FStar_Extraction_ML_UEnv.extend_type_name env
                                fv
                               in
                            (uu____70578, (iface_of_type_names [fv]))
                          else
                            (let uu____70581 =
                               FStar_Extraction_ML_UEnv.extend_tydef env fv
                                 td
                                in
                             match uu____70581 with
                             | (env2,tydef) ->
                                 let uu____70592 = iface_of_tydefs [tydef]
                                    in
                                 (env2, uu____70592))
                           in
                        (match uu____70556 with
                         | (env2,iface1) -> (env2, iface1, def2))))
  
let (extract_bundle_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt -> (env_t * iface))
  =
  fun env  ->
    fun se  ->
      let extract_ctor env_iparams ml_tyvars env1 ctor =
        let mlt =
          let uu____70668 =
            FStar_Extraction_ML_Term.term_as_mlty env_iparams ctor.dtyp  in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env_iparams) uu____70668
           in
        let tys = (ml_tyvars, mlt)  in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp  in
        let uu____70675 =
          FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false  in
        match uu____70675 with | (env2,uu____70694,b) -> (env2, (fvv, b))  in
      let extract_one_family env1 ind =
        let uu____70733 = binders_as_mlty_binders env1 ind.iparams  in
        match uu____70733 with
        | (env_iparams,vars) ->
            let uu____70761 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor env_iparams vars) env1)
               in
            (match uu____70761 with | (env2,ctors) -> (env2, ctors))
         in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____70825,t,uu____70827,uu____70828,uu____70829);
            FStar_Syntax_Syntax.sigrng = uu____70830;
            FStar_Syntax_Syntax.sigquals = uu____70831;
            FStar_Syntax_Syntax.sigmeta = uu____70832;
            FStar_Syntax_Syntax.sigattrs = uu____70833;_}::[],uu____70834),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____70853 = extract_ctor env [] env { dname = l; dtyp = t }
             in
          (match uu____70853 with
           | (env1,ctor) -> (env1, (iface_of_bindings [ctor])))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____70886),quals) ->
          let uu____70900 =
            bundle_as_inductive_families env ses quals
              se.FStar_Syntax_Syntax.sigattrs
             in
          (match uu____70900 with
           | (env1,ifams) ->
               let uu____70917 =
                 FStar_Util.fold_map extract_one_family env1 ifams  in
               (match uu____70917 with
                | (env2,td) ->
                    let uu____70958 =
                      let uu____70959 =
                        let uu____70960 =
                          FStar_List.map (fun x  -> x.ifv) ifams  in
                        iface_of_type_names uu____70960  in
                      iface_union uu____70959
                        (iface_of_bindings (FStar_List.flatten td))
                       in
                    (env2, uu____70958)))
      | uu____70969 -> failwith "Unexpected signature element"
  
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
              let uu____71044 =
                let uu____71046 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun uu___618_71052  ->
                          match uu___618_71052 with
                          | FStar_Syntax_Syntax.Assumption  -> true
                          | uu____71055 -> false))
                   in
                Prims.op_Negation uu____71046  in
              if uu____71044
              then (g, empty_iface, [])
              else
                (let uu____71070 = FStar_Syntax_Util.arrow_formals t  in
                 match uu____71070 with
                 | (bs,uu____71094) ->
                     let fv =
                       FStar_Syntax_Syntax.lid_as_fv lid
                         FStar_Syntax_Syntax.delta_constant
                         FStar_Pervasives_Native.None
                        in
                     let lb =
                       let uu____71117 =
                         FStar_Syntax_Util.abs bs FStar_Syntax_Syntax.t_unit
                           FStar_Pervasives_Native.None
                          in
                       {
                         FStar_Syntax_Syntax.lbname = (FStar_Util.Inr fv);
                         FStar_Syntax_Syntax.lbunivs = univs1;
                         FStar_Syntax_Syntax.lbtyp = t;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_Tot_lid;
                         FStar_Syntax_Syntax.lbdef = uu____71117;
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
        let uu____71180 =
          FStar_Extraction_ML_UEnv.extend_fv' g1 fv ml_name tysc false false
           in
        match uu____71180 with
        | (g2,mangled_name,exp_binding) ->
            ((let uu____71202 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g2.FStar_Extraction_ML_UEnv.env_tcenv)
                  (FStar_Options.Other "ExtractionReify")
                 in
              if uu____71202
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
        (let uu____71238 =
           FStar_All.pipe_left
             (FStar_TypeChecker_Env.debug
                g.FStar_Extraction_ML_UEnv.env_tcenv)
             (FStar_Options.Other "ExtractionReify")
            in
         if uu____71238
         then
           let uu____71243 = FStar_Syntax_Print.term_to_string tm  in
           FStar_Util.print1 "extract_fv term: %s\n" uu____71243
         else ());
        (let uu____71248 =
           let uu____71249 = FStar_Syntax_Subst.compress tm  in
           uu____71249.FStar_Syntax_Syntax.n  in
         match uu____71248 with
         | FStar_Syntax_Syntax.Tm_uinst (tm1,uu____71257) -> extract_fv tm1
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             let mlp =
               FStar_Extraction_ML_Syntax.mlpath_of_lident
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             let uu____71264 = FStar_Extraction_ML_UEnv.lookup_fv g fv  in
             (match uu____71264 with
              | { FStar_Extraction_ML_UEnv.exp_b_name = uu____71269;
                  FStar_Extraction_ML_UEnv.exp_b_expr = uu____71270;
                  FStar_Extraction_ML_UEnv.exp_b_tscheme = tysc;
                  FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____71272;_} ->
                  let uu____71275 =
                    FStar_All.pipe_left
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.MLTY_Top)
                      (FStar_Extraction_ML_Syntax.MLE_Name mlp)
                     in
                  (uu____71275, tysc))
         | uu____71276 ->
             let uu____71277 =
               let uu____71279 =
                 FStar_Range.string_of_range tm.FStar_Syntax_Syntax.pos  in
               let uu____71281 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.format2 "(%s) Not an fv: %s" uu____71279
                 uu____71281
                in
             failwith uu____71277)
         in
      let extract_action g1 a =
        (let uu____71309 =
           FStar_All.pipe_left
             (FStar_TypeChecker_Env.debug
                g1.FStar_Extraction_ML_UEnv.env_tcenv)
             (FStar_Options.Other "ExtractionReify")
            in
         if uu____71309
         then
           let uu____71314 =
             FStar_Syntax_Print.term_to_string
               a.FStar_Syntax_Syntax.action_typ
              in
           let uu____71316 =
             FStar_Syntax_Print.term_to_string
               a.FStar_Syntax_Syntax.action_defn
              in
           FStar_Util.print2 "Action type %s and term %s\n" uu____71314
             uu____71316
         else ());
        (let uu____71321 = FStar_Extraction_ML_UEnv.action_name ed a  in
         match uu____71321 with
         | (a_nm,a_lid) ->
             let lbname =
               let uu____71341 =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some
                      ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                   FStar_Syntax_Syntax.tun
                  in
               FStar_Util.Inl uu____71341  in
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
             let uu____71371 =
               FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb  in
             (match uu____71371 with
              | (a_let,uu____71387,ty) ->
                  ((let uu____71390 =
                      FStar_All.pipe_left
                        (FStar_TypeChecker_Env.debug
                           g1.FStar_Extraction_ML_UEnv.env_tcenv)
                        (FStar_Options.Other "ExtractionReify")
                       in
                    if uu____71390
                    then
                      let uu____71395 =
                        FStar_Extraction_ML_Code.string_of_mlexpr a_nm a_let
                         in
                      FStar_Util.print1 "Extracted action term: %s\n"
                        uu____71395
                    else ());
                   (let uu____71400 =
                      match a_let.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Let
                          ((uu____71423,mllb::[]),uu____71425) ->
                          (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc
                           with
                           | FStar_Pervasives_Native.Some tysc ->
                               ((mllb.FStar_Extraction_ML_Syntax.mllb_def),
                                 tysc)
                           | FStar_Pervasives_Native.None  ->
                               failwith "No type scheme")
                      | uu____71465 -> failwith "Impossible"  in
                    match uu____71400 with
                    | (exp,tysc) ->
                        ((let uu____71503 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug
                                 g1.FStar_Extraction_ML_UEnv.env_tcenv)
                              (FStar_Options.Other "ExtractionReify")
                             in
                          if uu____71503
                          then
                            ((let uu____71509 =
                                FStar_Extraction_ML_Code.string_of_mlty a_nm
                                  (FStar_Pervasives_Native.snd tysc)
                                 in
                              FStar_Util.print1 "Extracted action type: %s\n"
                                uu____71509);
                             FStar_List.iter
                               (fun x  ->
                                  FStar_Util.print1 "and binders: %s\n" x)
                               (FStar_Pervasives_Native.fst tysc))
                          else ());
                         (let uu____71525 = extend_env g1 a_lid a_nm exp tysc
                             in
                          match uu____71525 with
                          | (env,iface1,impl) -> (env, (iface1, impl))))))))
         in
      let uu____71547 =
        let uu____71554 =
          extract_fv
            (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.return_repr)
           in
        match uu____71554 with
        | (return_tm,ty_sc) ->
            let uu____71571 =
              FStar_Extraction_ML_UEnv.monad_op_name ed "return"  in
            (match uu____71571 with
             | (return_nm,return_lid) ->
                 extend_env g return_lid return_nm return_tm ty_sc)
         in
      match uu____71547 with
      | (g1,return_iface,return_decl) ->
          let uu____71596 =
            let uu____71603 =
              extract_fv
                (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.bind_repr)
               in
            match uu____71603 with
            | (bind_tm,ty_sc) ->
                let uu____71620 =
                  FStar_Extraction_ML_UEnv.monad_op_name ed "bind"  in
                (match uu____71620 with
                 | (bind_nm,bind_lid) ->
                     extend_env g1 bind_lid bind_nm bind_tm ty_sc)
             in
          (match uu____71596 with
           | (g2,bind_iface,bind_decl) ->
               let uu____71645 =
                 FStar_Util.fold_map extract_action g2
                   ed.FStar_Syntax_Syntax.actions
                  in
               (match uu____71645 with
                | (g3,actions) ->
                    let uu____71682 = FStar_List.unzip actions  in
                    (match uu____71682 with
                     | (actions_iface,actions1) ->
                         let uu____71709 =
                           iface_union_l (return_iface :: bind_iface ::
                             actions_iface)
                            in
                         (g3, uu____71709, (return_decl :: bind_decl ::
                           actions1)))))
  
let (extract_sigelt_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle uu____71731 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____71740 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_datacon uu____71757 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) when
          FStar_Extraction_ML_Term.is_arity g t ->
          let uu____71776 =
            extract_type_declaration g lid se.FStar_Syntax_Syntax.sigquals
              se.FStar_Syntax_Syntax.sigattrs univs1 t
             in
          (match uu____71776 with | (env,iface1,uu____71791) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____71797) when
          FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp ->
          let uu____71806 =
            extract_typ_abbrev g se.FStar_Syntax_Syntax.sigquals
              se.FStar_Syntax_Syntax.sigattrs lb
             in
          (match uu____71806 with | (env,iface1,uu____71821) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,_univs,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let uu____71832 =
            (FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption))
              &&
              (let uu____71838 =
                 FStar_TypeChecker_Util.must_erase_for_extraction
                   g.FStar_Extraction_ML_UEnv.env_tcenv t
                  in
               Prims.op_Negation uu____71838)
             in
          if uu____71832
          then
            let uu____71845 =
              let uu____71856 =
                let uu____71857 =
                  let uu____71860 = always_fail lid t  in [uu____71860]  in
                (false, uu____71857)  in
              FStar_Extraction_ML_Term.extract_lb_iface g uu____71856  in
            (match uu____71845 with
             | (g1,bindings) -> (g1, (iface_of_bindings bindings)))
          else (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____71886) ->
          let uu____71891 = FStar_Extraction_ML_Term.extract_lb_iface g lbs
             in
          (match uu____71891 with
           | (g1,bindings) -> (g1, (iface_of_bindings bindings)))
      | FStar_Syntax_Syntax.Sig_main uu____71920 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____71921 ->
          (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_assume uu____71922 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____71929 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____71930 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          (FStar_Syntax_Util.process_pragma p se.FStar_Syntax_Syntax.sigrng;
           (g, empty_iface))
      | FStar_Syntax_Syntax.Sig_splice uu____71945 ->
          failwith "impossible: trying to extract splice"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____71958 =
            (FStar_TypeChecker_Env.is_reifiable_effect
               g.FStar_Extraction_ML_UEnv.env_tcenv
               ed.FStar_Syntax_Syntax.mname)
              && (FStar_List.isEmpty ed.FStar_Syntax_Syntax.binders)
             in
          if uu____71958
          then
            let uu____71971 = extract_reifiable_effect g ed  in
            (match uu____71971 with
             | (env,iface1,uu____71986) -> (env, iface1))
          else (g, empty_iface)
  
let (extract_iface' :
  env_t ->
    FStar_Syntax_Syntax.modul -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun modul  ->
      let uu____72008 = FStar_Options.interactive ()  in
      if uu____72008
      then (g, empty_iface)
      else
        (let uu____72017 = FStar_Options.restore_cmd_line_options true  in
         let decls = modul.FStar_Syntax_Syntax.declarations  in
         let iface1 =
           let uu___1165_72021 = empty_iface  in
           {
             iface_module_name = (g.FStar_Extraction_ML_UEnv.currentModule);
             iface_bindings = (uu___1165_72021.iface_bindings);
             iface_tydefs = (uu___1165_72021.iface_tydefs);
             iface_type_names = (uu___1165_72021.iface_type_names)
           }  in
         let res =
           FStar_List.fold_left
             (fun uu____72039  ->
                fun se  ->
                  match uu____72039 with
                  | (g1,iface2) ->
                      let uu____72051 = extract_sigelt_iface g1 se  in
                      (match uu____72051 with
                       | (g2,iface') ->
                           let uu____72062 = iface_union iface2 iface'  in
                           (g2, uu____72062))) (g, iface1) decls
            in
         (let uu____72064 = FStar_Options.restore_cmd_line_options true  in
          FStar_All.pipe_left (fun a1  -> ()) uu____72064);
         res)
  
let (extract_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.modul -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun modul  ->
      let uu____72081 = FStar_Options.debug_any ()  in
      if uu____72081
      then
        let uu____72088 =
          FStar_Util.format1 "Extracted interface of %s"
            (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
           in
        FStar_Util.measure_execution_time uu____72088
          (fun uu____72096  -> extract_iface' g modul)
      else extract_iface' g modul
  
let (extend_with_iface :
  FStar_Extraction_ML_UEnv.uenv -> iface -> FStar_Extraction_ML_UEnv.uenv) =
  fun g  ->
    fun iface1  ->
      let uu___1183_72110 = g  in
      let uu____72111 =
        let uu____72114 =
          FStar_List.map (fun _72121  -> FStar_Extraction_ML_UEnv.Fv _72121)
            iface1.iface_bindings
           in
        FStar_List.append uu____72114 g.FStar_Extraction_ML_UEnv.env_bindings
         in
      {
        FStar_Extraction_ML_UEnv.env_tcenv =
          (uu___1183_72110.FStar_Extraction_ML_UEnv.env_tcenv);
        FStar_Extraction_ML_UEnv.env_bindings = uu____72111;
        FStar_Extraction_ML_UEnv.tydefs =
          (FStar_List.append iface1.iface_tydefs
             g.FStar_Extraction_ML_UEnv.tydefs);
        FStar_Extraction_ML_UEnv.type_names =
          (FStar_List.append iface1.iface_type_names
             g.FStar_Extraction_ML_UEnv.type_names);
        FStar_Extraction_ML_UEnv.currentModule =
          (uu___1183_72110.FStar_Extraction_ML_UEnv.currentModule)
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
          let uu____72199 =
            FStar_Extraction_ML_Term.term_as_mlty env_iparams ctor.dtyp  in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env_iparams) uu____72199
           in
        let steps =
          [FStar_TypeChecker_Env.Inlining;
          FStar_TypeChecker_Env.UnfoldUntil
            FStar_Syntax_Syntax.delta_constant;
          FStar_TypeChecker_Env.EraseUniverses;
          FStar_TypeChecker_Env.AllowUnboundUniverses]  in
        let names1 =
          let uu____72207 =
            let uu____72208 =
              let uu____72211 =
                FStar_TypeChecker_Normalize.normalize steps
                  env_iparams.FStar_Extraction_ML_UEnv.env_tcenv ctor.dtyp
                 in
              FStar_Syntax_Subst.compress uu____72211  in
            uu____72208.FStar_Syntax_Syntax.n  in
          match uu____72207 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,uu____72216) ->
              FStar_List.map
                (fun uu____72249  ->
                   match uu____72249 with
                   | ({ FStar_Syntax_Syntax.ppname = ppname;
                        FStar_Syntax_Syntax.index = uu____72258;
                        FStar_Syntax_Syntax.sort = uu____72259;_},uu____72260)
                       -> ppname.FStar_Ident.idText) bs
          | uu____72268 -> []  in
        let tys = (ml_tyvars, mlt)  in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp  in
        let uu____72276 =
          FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false  in
        match uu____72276 with
        | (env2,uu____72303,uu____72304) ->
            let uu____72307 =
              let uu____72320 = lident_as_mlsymbol ctor.dname  in
              let uu____72322 =
                let uu____72330 = FStar_Extraction_ML_Util.argTypes mlt  in
                FStar_List.zip names1 uu____72330  in
              (uu____72320, uu____72322)  in
            (env2, uu____72307)
         in
      let extract_one_family env1 ind =
        let uu____72391 = binders_as_mlty_binders env1 ind.iparams  in
        match uu____72391 with
        | (env_iparams,vars) ->
            let uu____72435 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor env_iparams vars) env1)
               in
            (match uu____72435 with
             | (env2,ctors) ->
                 let uu____72542 = FStar_Syntax_Util.arrow_formals ind.ityp
                    in
                 (match uu____72542 with
                  | (indices,uu____72584) ->
                      let ml_params =
                        let uu____72609 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____72635  ->
                                    let uu____72643 =
                                      FStar_Util.string_of_int i  in
                                    Prims.op_Hat "'dummyV" uu____72643))
                           in
                        FStar_List.append vars uu____72609  in
                      let tbody =
                        let uu____72648 =
                          FStar_Util.find_opt
                            (fun uu___619_72653  ->
                               match uu___619_72653 with
                               | FStar_Syntax_Syntax.RecordType uu____72655
                                   -> true
                               | uu____72665 -> false) ind.iquals
                           in
                        match uu____72648 with
                        | FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                            let uu____72677 = FStar_List.hd ctors  in
                            (match uu____72677 with
                             | (uu____72702,c_ty) ->
                                 let fields =
                                   FStar_List.map2
                                     (fun id1  ->
                                        fun uu____72746  ->
                                          match uu____72746 with
                                          | (uu____72757,ty) ->
                                              let lid =
                                                FStar_Ident.lid_of_ids
                                                  (FStar_List.append ns [id1])
                                                 in
                                              let uu____72762 =
                                                lident_as_mlsymbol lid  in
                                              (uu____72762, ty)) ids c_ty
                                    in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____72765 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors
                         in
                      let uu____72768 =
                        let uu____72791 = lident_as_mlsymbol ind.iname  in
                        (false, uu____72791, FStar_Pervasives_Native.None,
                          ml_params, (ind.imetadata),
                          (FStar_Pervasives_Native.Some tbody))
                         in
                      (env2, uu____72768)))
         in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____72836,t,uu____72838,uu____72839,uu____72840);
            FStar_Syntax_Syntax.sigrng = uu____72841;
            FStar_Syntax_Syntax.sigquals = uu____72842;
            FStar_Syntax_Syntax.sigmeta = uu____72843;
            FStar_Syntax_Syntax.sigattrs = uu____72844;_}::[],uu____72845),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____72864 = extract_ctor env [] env { dname = l; dtyp = t }
             in
          (match uu____72864 with
           | (env1,ctor) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____72917),quals) ->
          let uu____72931 =
            bundle_as_inductive_families env ses quals
              se.FStar_Syntax_Syntax.sigattrs
             in
          (match uu____72931 with
           | (env1,ifams) ->
               let uu____72950 =
                 FStar_Util.fold_map extract_one_family env1 ifams  in
               (match uu____72950 with
                | (env2,td) -> (env2, [FStar_Extraction_ML_Syntax.MLM_Ty td])))
      | uu____73059 -> failwith "Unexpected signature element"
  
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
             let uu____73117 = FStar_Syntax_Util.head_and_args t  in
             match uu____73117 with
             | (head1,args) ->
                 let uu____73165 =
                   let uu____73167 =
                     FStar_Syntax_Util.is_fvar FStar_Parser_Const.plugin_attr
                       head1
                      in
                   Prims.op_Negation uu____73167  in
                 if uu____73165
                 then FStar_Pervasives_Native.None
                 else
                   (match args with
                    | ({
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_int (s,uu____73186));
                         FStar_Syntax_Syntax.pos = uu____73187;
                         FStar_Syntax_Syntax.vars = uu____73188;_},uu____73189)::[]
                        ->
                        let uu____73228 =
                          let uu____73232 = FStar_Util.int_of_string s  in
                          FStar_Pervasives_Native.Some uu____73232  in
                        FStar_Pervasives_Native.Some uu____73228
                    | uu____73238 ->
                        FStar_Pervasives_Native.Some
                          FStar_Pervasives_Native.None))
         in
      let uu____73253 =
        let uu____73255 = FStar_Options.codegen ()  in
        uu____73255 <> (FStar_Pervasives_Native.Some FStar_Options.Plugin)
         in
      if uu____73253
      then []
      else
        (let uu____73265 = plugin_with_arity se.FStar_Syntax_Syntax.sigattrs
            in
         match uu____73265 with
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
                      let uu____73307 =
                        let uu____73308 = FStar_Ident.string_of_lid fv_lid1
                           in
                        FStar_Extraction_ML_Syntax.MLC_String uu____73308  in
                      FStar_Extraction_ML_Syntax.MLE_Const uu____73307  in
                    let uu____73310 =
                      FStar_Extraction_ML_Util.interpret_plugin_as_term_fun
                        g.FStar_Extraction_ML_UEnv.env_tcenv fv fv_t
                        arity_opt ml_name_str
                       in
                    match uu____73310 with
                    | FStar_Pervasives_Native.Some
                        (interp,nbe_interp,arity,plugin1) ->
                        let uu____73343 =
                          if plugin1
                          then
                            ("FStar_Tactics_Native.register_plugin",
                              [interp; nbe_interp])
                          else
                            ("FStar_Tactics_Native.register_tactic",
                              [interp])
                           in
                        (match uu____73343 with
                         | (register,args) ->
                             let h =
                               let uu____73380 =
                                 let uu____73381 =
                                   let uu____73382 =
                                     FStar_Ident.lid_of_str register  in
                                   FStar_Extraction_ML_Syntax.mlpath_of_lident
                                     uu____73382
                                    in
                                 FStar_Extraction_ML_Syntax.MLE_Name
                                   uu____73381
                                  in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    FStar_Extraction_ML_Syntax.MLTY_Top)
                                 uu____73380
                                in
                             let arity1 =
                               let uu____73384 =
                                 let uu____73385 =
                                   let uu____73397 =
                                     FStar_Util.string_of_int arity  in
                                   (uu____73397,
                                     FStar_Pervasives_Native.None)
                                    in
                                 FStar_Extraction_ML_Syntax.MLC_Int
                                   uu____73385
                                  in
                               FStar_Extraction_ML_Syntax.MLE_Const
                                 uu____73384
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
              | uu____73426 -> []))
  
let rec (extract_sig :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list))
  =
  fun g  ->
    fun se  ->
      FStar_Extraction_ML_UEnv.debug g
        (fun u  ->
           let uu____73454 = FStar_Syntax_Print.sigelt_to_string se  in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____73454);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle uu____73463 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____73472 ->
           extract_bundle g se
       | FStar_Syntax_Syntax.Sig_datacon uu____73489 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           FStar_TypeChecker_Env.is_reifiable_effect
             g.FStar_Extraction_ML_UEnv.env_tcenv
             ed.FStar_Syntax_Syntax.mname
           ->
           let uu____73506 = extract_reifiable_effect g ed  in
           (match uu____73506 with | (env,_iface,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_splice uu____73530 ->
           failwith "impossible: trying to extract splice"
       | FStar_Syntax_Syntax.Sig_new_effect uu____73544 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let uu____73550 =
             extract_type_declaration g lid se.FStar_Syntax_Syntax.sigquals
               se.FStar_Syntax_Syntax.sigattrs univs1 t
              in
           (match uu____73550 with | (env,uu____73566,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____73575) when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let uu____73584 =
             extract_typ_abbrev g se.FStar_Syntax_Syntax.sigquals
               se.FStar_Syntax_Syntax.sigattrs lb
              in
           (match uu____73584 with | (env,uu____73600,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____73609) ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____73620 =
             let uu____73629 =
               FStar_Syntax_Util.extract_attr'
                 FStar_Parser_Const.postprocess_extr_with attrs
                in
             match uu____73629 with
             | FStar_Pervasives_Native.None  ->
                 (attrs, FStar_Pervasives_Native.None)
             | FStar_Pervasives_Native.Some
                 (ats,(tau,FStar_Pervasives_Native.None )::uu____73658) ->
                 (ats, (FStar_Pervasives_Native.Some tau))
             | FStar_Pervasives_Native.Some (ats,args) ->
                 (FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng
                    (FStar_Errors.Warning_UnrecognizedAttribute,
                      "Ill-formed application of `postprocess_for_extraction_with`");
                  (attrs, FStar_Pervasives_Native.None))
              in
           (match uu____73620 with
            | (attrs1,post_tau) ->
                let postprocess_lb tau lb =
                  let lbdef =
                    FStar_TypeChecker_Env.postprocess
                      g.FStar_Extraction_ML_UEnv.env_tcenv tau
                      lb.FStar_Syntax_Syntax.lbtyp
                      lb.FStar_Syntax_Syntax.lbdef
                     in
                  let uu___1402_73744 = lb  in
                  {
                    FStar_Syntax_Syntax.lbname =
                      (uu___1402_73744.FStar_Syntax_Syntax.lbname);
                    FStar_Syntax_Syntax.lbunivs =
                      (uu___1402_73744.FStar_Syntax_Syntax.lbunivs);
                    FStar_Syntax_Syntax.lbtyp =
                      (uu___1402_73744.FStar_Syntax_Syntax.lbtyp);
                    FStar_Syntax_Syntax.lbeff =
                      (uu___1402_73744.FStar_Syntax_Syntax.lbeff);
                    FStar_Syntax_Syntax.lbdef = lbdef;
                    FStar_Syntax_Syntax.lbattrs =
                      (uu___1402_73744.FStar_Syntax_Syntax.lbattrs);
                    FStar_Syntax_Syntax.lbpos =
                      (uu___1402_73744.FStar_Syntax_Syntax.lbpos)
                  }  in
                let lbs1 =
                  let uu____73753 =
                    match post_tau with
                    | FStar_Pervasives_Native.Some tau ->
                        FStar_List.map (postprocess_lb tau)
                          (FStar_Pervasives_Native.snd lbs)
                    | FStar_Pervasives_Native.None  ->
                        FStar_Pervasives_Native.snd lbs
                     in
                  ((FStar_Pervasives_Native.fst lbs), uu____73753)  in
                let uu____73771 =
                  let uu____73778 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_let
                         (lbs1, FStar_Syntax_Util.exp_false_bool))
                      FStar_Pervasives_Native.None
                      se.FStar_Syntax_Syntax.sigrng
                     in
                  FStar_Extraction_ML_Term.term_as_mlexpr g uu____73778  in
                (match uu____73771 with
                 | (ml_let,uu____73795,uu____73796) ->
                     (match ml_let.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Let
                          ((flavor,bindings),uu____73805) ->
                          let flags = FStar_List.choose flag_of_qual quals
                             in
                          let flags' = extract_metadata attrs1  in
                          let uu____73822 =
                            FStar_List.fold_left2
                              (fun uu____73848  ->
                                 fun ml_lb  ->
                                   fun uu____73850  ->
                                     match (uu____73848, uu____73850) with
                                     | ((env,ml_lbs),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbname;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uu____73872;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = t;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____73874;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = uu____73875;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____73876;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____73877;_})
                                         ->
                                         let uu____73902 =
                                           FStar_All.pipe_right
                                             ml_lb.FStar_Extraction_ML_Syntax.mllb_meta
                                             (FStar_List.contains
                                                FStar_Extraction_ML_Syntax.Erased)
                                            in
                                         if uu____73902
                                         then (env, ml_lbs)
                                         else
                                           (let lb_lid =
                                              let uu____73919 =
                                                let uu____73922 =
                                                  FStar_Util.right lbname  in
                                                uu____73922.FStar_Syntax_Syntax.fv_name
                                                 in
                                              uu____73919.FStar_Syntax_Syntax.v
                                               in
                                            let flags'' =
                                              let uu____73926 =
                                                let uu____73927 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____73927.FStar_Syntax_Syntax.n
                                                 in
                                              match uu____73926 with
                                              | FStar_Syntax_Syntax.Tm_arrow
                                                  (uu____73932,{
                                                                 FStar_Syntax_Syntax.n
                                                                   =
                                                                   FStar_Syntax_Syntax.Comp
                                                                   {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____73933;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    = e;
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    =
                                                                    uu____73935;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____73936;
                                                                    FStar_Syntax_Syntax.flags
                                                                    =
                                                                    uu____73937;_};
                                                                 FStar_Syntax_Syntax.pos
                                                                   =
                                                                   uu____73938;
                                                                 FStar_Syntax_Syntax.vars
                                                                   =
                                                                   uu____73939;_})
                                                  when
                                                  let uu____73974 =
                                                    FStar_Ident.string_of_lid
                                                      e
                                                     in
                                                  uu____73974 =
                                                    "FStar.HyperStack.ST.StackInline"
                                                  ->
                                                  [FStar_Extraction_ML_Syntax.StackInline]
                                              | uu____73978 -> []  in
                                            let meta =
                                              FStar_List.append flags
                                                (FStar_List.append flags'
                                                   flags'')
                                               in
                                            let ml_lb1 =
                                              let uu___1450_73983 = ml_lb  in
                                              {
                                                FStar_Extraction_ML_Syntax.mllb_name
                                                  =
                                                  (uu___1450_73983.FStar_Extraction_ML_Syntax.mllb_name);
                                                FStar_Extraction_ML_Syntax.mllb_tysc
                                                  =
                                                  (uu___1450_73983.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                FStar_Extraction_ML_Syntax.mllb_add_unit
                                                  =
                                                  (uu___1450_73983.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                FStar_Extraction_ML_Syntax.mllb_def
                                                  =
                                                  (uu___1450_73983.FStar_Extraction_ML_Syntax.mllb_def);
                                                FStar_Extraction_ML_Syntax.mllb_meta
                                                  = meta;
                                                FStar_Extraction_ML_Syntax.print_typ
                                                  =
                                                  (uu___1450_73983.FStar_Extraction_ML_Syntax.print_typ)
                                              }  in
                                            let uu____73984 =
                                              let uu____73989 =
                                                FStar_All.pipe_right quals
                                                  (FStar_Util.for_some
                                                     (fun uu___620_73996  ->
                                                        match uu___620_73996
                                                        with
                                                        | FStar_Syntax_Syntax.Projector
                                                            uu____73998 ->
                                                            true
                                                        | uu____74004 ->
                                                            false))
                                                 in
                                              if uu____73989
                                              then
                                                let mname =
                                                  let uu____74020 =
                                                    mangle_projector_lid
                                                      lb_lid
                                                     in
                                                  FStar_All.pipe_right
                                                    uu____74020
                                                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                                                   in
                                                let uu____74029 =
                                                  let uu____74037 =
                                                    FStar_Util.right lbname
                                                     in
                                                  let uu____74038 =
                                                    FStar_Util.must
                                                      ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc
                                                     in
                                                  FStar_Extraction_ML_UEnv.extend_fv'
                                                    env uu____74037 mname
                                                    uu____74038
                                                    ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                                    false
                                                   in
                                                match uu____74029 with
                                                | (env1,uu____74045,uu____74046)
                                                    ->
                                                    (env1,
                                                      (let uu___1463_74050 =
                                                         ml_lb1  in
                                                       {
                                                         FStar_Extraction_ML_Syntax.mllb_name
                                                           =
                                                           (FStar_Pervasives_Native.snd
                                                              mname);
                                                         FStar_Extraction_ML_Syntax.mllb_tysc
                                                           =
                                                           (uu___1463_74050.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                         FStar_Extraction_ML_Syntax.mllb_add_unit
                                                           =
                                                           (uu___1463_74050.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                         FStar_Extraction_ML_Syntax.mllb_def
                                                           =
                                                           (uu___1463_74050.FStar_Extraction_ML_Syntax.mllb_def);
                                                         FStar_Extraction_ML_Syntax.mllb_meta
                                                           =
                                                           (uu___1463_74050.FStar_Extraction_ML_Syntax.mllb_meta);
                                                         FStar_Extraction_ML_Syntax.print_typ
                                                           =
                                                           (uu___1463_74050.FStar_Extraction_ML_Syntax.print_typ)
                                                       }))
                                              else
                                                (let uu____74057 =
                                                   let uu____74065 =
                                                     FStar_Util.must
                                                       ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc
                                                      in
                                                   FStar_Extraction_ML_UEnv.extend_lb
                                                     env lbname t uu____74065
                                                     ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                                     false
                                                    in
                                                 match uu____74057 with
                                                 | (env1,uu____74072,uu____74073)
                                                     -> (env1, ml_lb1))
                                               in
                                            match uu____73984 with
                                            | (g1,ml_lb2) ->
                                                (g1, (ml_lb2 :: ml_lbs))))
                              (g, []) bindings
                              (FStar_Pervasives_Native.snd lbs1)
                             in
                          (match uu____73822 with
                           | (g1,ml_lbs') ->
                               let uu____74103 =
                                 let uu____74106 =
                                   let uu____74109 =
                                     let uu____74110 =
                                       FStar_Extraction_ML_Util.mlloc_of_range
                                         se.FStar_Syntax_Syntax.sigrng
                                        in
                                     FStar_Extraction_ML_Syntax.MLM_Loc
                                       uu____74110
                                      in
                                   [uu____74109;
                                   FStar_Extraction_ML_Syntax.MLM_Let
                                     (flavor, (FStar_List.rev ml_lbs'))]
                                    in
                                 let uu____74113 =
                                   maybe_register_plugin g1 se  in
                                 FStar_List.append uu____74106 uu____74113
                                  in
                               (g1, uu____74103))
                      | uu____74118 ->
                          let uu____74119 =
                            let uu____74121 =
                              FStar_Extraction_ML_Code.string_of_mlexpr
                                g.FStar_Extraction_ML_UEnv.currentModule
                                ml_let
                               in
                            FStar_Util.format1
                              "Impossible: Translated a let to a non-let: %s"
                              uu____74121
                             in
                          failwith uu____74119)))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____74131,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____74136 =
             (FStar_All.pipe_right quals
                (FStar_List.contains FStar_Syntax_Syntax.Assumption))
               &&
               (let uu____74142 =
                  FStar_TypeChecker_Util.must_erase_for_extraction
                    g.FStar_Extraction_ML_UEnv.env_tcenv t
                   in
                Prims.op_Negation uu____74142)
              in
           if uu____74136
           then
             let always_fail1 =
               let uu___1483_74152 = se  in
               let uu____74153 =
                 let uu____74154 =
                   let uu____74161 =
                     let uu____74162 =
                       let uu____74165 = always_fail lid t  in [uu____74165]
                        in
                     (false, uu____74162)  in
                   (uu____74161, [])  in
                 FStar_Syntax_Syntax.Sig_let uu____74154  in
               {
                 FStar_Syntax_Syntax.sigel = uu____74153;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___1483_74152.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___1483_74152.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___1483_74152.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___1483_74152.FStar_Syntax_Syntax.sigattrs)
               }  in
             let uu____74172 = extract_sig g always_fail1  in
             (match uu____74172 with
              | (g1,mlm) ->
                  let uu____74191 =
                    FStar_Util.find_map quals
                      (fun uu___621_74196  ->
                         match uu___621_74196 with
                         | FStar_Syntax_Syntax.Discriminator l ->
                             FStar_Pervasives_Native.Some l
                         | uu____74200 -> FStar_Pervasives_Native.None)
                     in
                  (match uu____74191 with
                   | FStar_Pervasives_Native.Some l ->
                       let uu____74208 =
                         let uu____74211 =
                           let uu____74212 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng
                              in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____74212  in
                         let uu____74213 =
                           let uu____74216 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l
                              in
                           [uu____74216]  in
                         uu____74211 :: uu____74213  in
                       (g1, uu____74208)
                   | uu____74219 ->
                       let uu____74222 =
                         FStar_Util.find_map quals
                           (fun uu___622_74228  ->
                              match uu___622_74228 with
                              | FStar_Syntax_Syntax.Projector (l,uu____74232)
                                  -> FStar_Pervasives_Native.Some l
                              | uu____74233 -> FStar_Pervasives_Native.None)
                          in
                       (match uu____74222 with
                        | FStar_Pervasives_Native.Some uu____74240 ->
                            (g1, [])
                        | uu____74243 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____74253 = FStar_Extraction_ML_Term.term_as_mlexpr g e  in
           (match uu____74253 with
            | (ml_main,uu____74267,uu____74268) ->
                let uu____74269 =
                  let uu____74272 =
                    let uu____74273 =
                      FStar_Extraction_ML_Util.mlloc_of_range
                        se.FStar_Syntax_Syntax.sigrng
                       in
                    FStar_Extraction_ML_Syntax.MLM_Loc uu____74273  in
                  [uu____74272; FStar_Extraction_ML_Syntax.MLM_Top ml_main]
                   in
                (g, uu____74269))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____74276 ->
           failwith "impossible -- removed by tc.fs"
       | FStar_Syntax_Syntax.Sig_assume uu____74284 -> (g, [])
       | FStar_Syntax_Syntax.Sig_sub_effect uu____74293 -> (g, [])
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____74296 -> (g, [])
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
      let uu____74338 = FStar_Options.restore_cmd_line_options true  in
      let name =
        FStar_Extraction_ML_Syntax.mlpath_of_lident
          m.FStar_Syntax_Syntax.name
         in
      let g1 =
        let uu___1526_74342 = g  in
        let uu____74343 =
          FStar_TypeChecker_Env.set_current_module
            g.FStar_Extraction_ML_UEnv.env_tcenv m.FStar_Syntax_Syntax.name
           in
        {
          FStar_Extraction_ML_UEnv.env_tcenv = uu____74343;
          FStar_Extraction_ML_UEnv.env_bindings =
            (uu___1526_74342.FStar_Extraction_ML_UEnv.env_bindings);
          FStar_Extraction_ML_UEnv.tydefs =
            (uu___1526_74342.FStar_Extraction_ML_UEnv.tydefs);
          FStar_Extraction_ML_UEnv.type_names =
            (uu___1526_74342.FStar_Extraction_ML_UEnv.type_names);
          FStar_Extraction_ML_UEnv.currentModule = name
        }  in
      let uu____74344 =
        FStar_Util.fold_map
          (fun g2  ->
             fun se  ->
               let uu____74363 =
                 FStar_Options.debug_module
                   (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                  in
               if uu____74363
               then
                 let nm =
                   let uu____74374 =
                     FStar_All.pipe_right
                       (FStar_Syntax_Util.lids_of_sigelt se)
                       (FStar_List.map FStar_Ident.string_of_lid)
                      in
                   FStar_All.pipe_right uu____74374
                     (FStar_String.concat ", ")
                    in
                 (FStar_Util.print1 "+++About to extract {%s}\n" nm;
                  (let uu____74391 =
                     FStar_Util.format1 "---Extracted {%s}" nm  in
                   FStar_Util.measure_execution_time uu____74391
                     (fun uu____74401  -> extract_sig g2 se)))
               else extract_sig g2 se) g1 m.FStar_Syntax_Syntax.declarations
         in
      match uu____74344 with
      | (g2,sigs) ->
          let mlm = FStar_List.flatten sigs  in
          let is_kremlin =
            let uu____74423 = FStar_Options.codegen ()  in
            uu____74423 =
              (FStar_Pervasives_Native.Some FStar_Options.Kremlin)
             in
          if
            ((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims") &&
              (is_kremlin ||
                 (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface))
          then
            ((let uu____74438 =
                let uu____74440 = FStar_Options.silent ()  in
                Prims.op_Negation uu____74440  in
              if uu____74438
              then
                let uu____74443 =
                  FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
                FStar_Util.print1 "Extracted module %s\n" uu____74443
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
      (let uu____74518 = FStar_Options.restore_cmd_line_options true  in
       FStar_All.pipe_left (fun a2  -> ()) uu____74518);
      (let uu____74521 =
         let uu____74523 =
           FStar_Options.should_extract
             (m.FStar_Syntax_Syntax.name).FStar_Ident.str
            in
         Prims.op_Negation uu____74523  in
       if uu____74521
       then
         let uu____74526 =
           let uu____74528 =
             FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
           FStar_Util.format1
             "Extract called on a module %s that should not be extracted"
             uu____74528
            in
         failwith uu____74526
       else ());
      (let uu____74533 = FStar_Options.interactive ()  in
       if uu____74533
       then (g, FStar_Pervasives_Native.None)
       else
         (let res =
            let uu____74553 = FStar_Options.debug_any ()  in
            if uu____74553
            then
              let msg =
                let uu____74564 =
                  FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name
                   in
                FStar_Util.format1 "Extracting module %s\n" uu____74564  in
              FStar_Util.measure_execution_time msg
                (fun uu____74574  -> extract' g m)
            else extract' g m  in
          (let uu____74578 = FStar_Options.restore_cmd_line_options true  in
           FStar_All.pipe_left (fun a3  -> ()) uu____74578);
          res))
  
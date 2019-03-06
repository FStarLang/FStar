open Prims
type env_t = FStar_Extraction_ML_UEnv.uenv
let (fail_exp :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun lid  ->
    fun t  ->
      let uu____64589 =
        let uu____64596 =
          let uu____64597 =
            let uu____64614 =
              FStar_Syntax_Syntax.fvar FStar_Parser_Const.failwith_lid
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            let uu____64617 =
              let uu____64628 = FStar_Syntax_Syntax.iarg t  in
              let uu____64637 =
                let uu____64648 =
                  let uu____64657 =
                    let uu____64658 =
                      let uu____64665 =
                        let uu____64666 =
                          let uu____64667 =
                            let uu____64673 =
                              let uu____64675 =
                                FStar_Syntax_Print.lid_to_string lid  in
                              Prims.op_Hat "Not yet implemented:" uu____64675
                               in
                            (uu____64673, FStar_Range.dummyRange)  in
                          FStar_Const.Const_string uu____64667  in
                        FStar_Syntax_Syntax.Tm_constant uu____64666  in
                      FStar_Syntax_Syntax.mk uu____64665  in
                    uu____64658 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange
                     in
                  FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____64657
                   in
                [uu____64648]  in
              uu____64628 :: uu____64637  in
            (uu____64614, uu____64617)  in
          FStar_Syntax_Syntax.Tm_app uu____64597  in
        FStar_Syntax_Syntax.mk uu____64596  in
      uu____64589 FStar_Pervasives_Native.None FStar_Range.dummyRange
  
let (always_fail :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.letbinding)
  =
  fun lid  ->
    fun t  ->
      let imp =
        let uu____64741 = FStar_Syntax_Util.arrow_formals t  in
        match uu____64741 with
        | ([],t1) ->
            let b =
              let uu____64784 =
                FStar_Syntax_Syntax.gen_bv "_" FStar_Pervasives_Native.None
                  t1
                 in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____64784
               in
            let uu____64792 = fail_exp lid t1  in
            FStar_Syntax_Util.abs [b] uu____64792
              FStar_Pervasives_Native.None
        | (bs,t1) ->
            let uu____64829 = fail_exp lid t1  in
            FStar_Syntax_Util.abs bs uu____64829 FStar_Pervasives_Native.None
         in
      let lb =
        let uu____64833 =
          let uu____64838 =
            FStar_Syntax_Syntax.lid_as_fv lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
             in
          FStar_Util.Inr uu____64838  in
        {
          FStar_Syntax_Syntax.lbname = uu____64833;
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
  'Auu____64860 . 'Auu____64860 Prims.list -> ('Auu____64860 * 'Auu____64860)
  =
  fun uu___612_64871  ->
    match uu___612_64871 with
    | a::b::[] -> (a, b)
    | uu____64876 -> failwith "Expected a list with 2 elements"
  
let (flag_of_qual :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option)
  =
  fun uu___613_64891  ->
    match uu___613_64891 with
    | FStar_Syntax_Syntax.Assumption  ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Assumed
    | FStar_Syntax_Syntax.Private  ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Private
    | FStar_Syntax_Syntax.NoExtract  ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.NoExtract
    | uu____64894 -> FStar_Pervasives_Native.None
  
let rec (extract_meta :
  FStar_Syntax_Syntax.term ->
    FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option)
  =
  fun x  ->
    let uu____64903 = FStar_Syntax_Subst.compress x  in
    match uu____64903 with
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
        FStar_Syntax_Syntax.pos = uu____64907;
        FStar_Syntax_Syntax.vars = uu____64908;_} ->
        let uu____64911 =
          let uu____64913 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____64913  in
        (match uu____64911 with
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
         | uu____64923 -> FStar_Pervasives_Native.None)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____64926;
             FStar_Syntax_Syntax.vars = uu____64927;_},({
                                                          FStar_Syntax_Syntax.n
                                                            =
                                                            FStar_Syntax_Syntax.Tm_constant
                                                            (FStar_Const.Const_string
                                                            (s,uu____64929));
                                                          FStar_Syntax_Syntax.pos
                                                            = uu____64930;
                                                          FStar_Syntax_Syntax.vars
                                                            = uu____64931;_},uu____64932)::[]);
        FStar_Syntax_Syntax.pos = uu____64933;
        FStar_Syntax_Syntax.vars = uu____64934;_} ->
        let uu____64977 =
          let uu____64979 = FStar_Syntax_Syntax.lid_of_fv fv  in
          FStar_Ident.string_of_lid uu____64979  in
        (match uu____64977 with
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
         | uu____64988 -> FStar_Pervasives_Native.None)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("KremlinPrivate",uu____64990));
        FStar_Syntax_Syntax.pos = uu____64991;
        FStar_Syntax_Syntax.vars = uu____64992;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Private
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("c_inline",uu____64997));
        FStar_Syntax_Syntax.pos = uu____64998;
        FStar_Syntax_Syntax.vars = uu____64999;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.CInline
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("substitute",uu____65004));
        FStar_Syntax_Syntax.pos = uu____65005;
        FStar_Syntax_Syntax.vars = uu____65006;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Substitute
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_meta (x1,uu____65012);
        FStar_Syntax_Syntax.pos = uu____65013;
        FStar_Syntax_Syntax.vars = uu____65014;_} -> extract_meta x1
    | uu____65021 -> FStar_Pervasives_Native.None
  
let (extract_metadata :
  FStar_Syntax_Syntax.term Prims.list ->
    FStar_Extraction_ML_Syntax.meta Prims.list)
  = fun metas  -> FStar_List.choose extract_meta metas 
let binders_as_mlty_binders :
  'Auu____65041 .
    FStar_Extraction_ML_UEnv.uenv ->
      (FStar_Syntax_Syntax.bv * 'Auu____65041) Prims.list ->
        (FStar_Extraction_ML_UEnv.uenv * Prims.string Prims.list)
  =
  fun env  ->
    fun bs  ->
      FStar_Util.fold_map
        (fun env1  ->
           fun uu____65083  ->
             match uu____65083 with
             | (bv,uu____65094) ->
                 let uu____65095 =
                   let uu____65096 =
                     let uu____65099 =
                       let uu____65100 =
                         FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv  in
                       FStar_Extraction_ML_Syntax.MLTY_Var uu____65100  in
                     FStar_Pervasives_Native.Some uu____65099  in
                   FStar_Extraction_ML_UEnv.extend_ty env1 bv uu____65096  in
                 let uu____65102 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv
                    in
                 (uu____65095, uu____65102)) env bs
  
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
    let uu____65303 = FStar_Syntax_Print.lid_to_string i.iname  in
    let uu____65305 = FStar_Syntax_Print.binders_to_string " " i.iparams  in
    let uu____65308 = FStar_Syntax_Print.term_to_string i.ityp  in
    let uu____65310 =
      let uu____65312 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d  ->
                let uu____65326 = FStar_Syntax_Print.lid_to_string d.dname
                   in
                let uu____65328 =
                  let uu____65330 = FStar_Syntax_Print.term_to_string d.dtyp
                     in
                  Prims.op_Hat " : " uu____65330  in
                Prims.op_Hat uu____65326 uu____65328))
         in
      FStar_All.pipe_right uu____65312 (FStar_String.concat "\n\t\t")  in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____65303 uu____65305
      uu____65308 uu____65310
  
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
          let uu____65384 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun se  ->
                   match se.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,_us,bs,t,_mut_i,datas) ->
                       let uu____65432 = FStar_Syntax_Subst.open_term bs t
                          in
                       (match uu____65432 with
                        | (bs1,t1) ->
                            let datas1 =
                              FStar_All.pipe_right ses
                                (FStar_List.collect
                                   (fun se1  ->
                                      match se1.FStar_Syntax_Syntax.sigel
                                      with
                                      | FStar_Syntax_Syntax.Sig_datacon
                                          (d,uu____65471,t2,l',nparams,uu____65475)
                                          when FStar_Ident.lid_equals l l' ->
                                          let uu____65482 =
                                            FStar_Syntax_Util.arrow_formals
                                              t2
                                             in
                                          (match uu____65482 with
                                           | (bs',body) ->
                                               let uu____65521 =
                                                 FStar_Util.first_N
                                                   (FStar_List.length bs1)
                                                   bs'
                                                  in
                                               (match uu____65521 with
                                                | (bs_params,rest) ->
                                                    let subst1 =
                                                      FStar_List.map2
                                                        (fun uu____65612  ->
                                                           fun uu____65613 
                                                             ->
                                                             match (uu____65612,
                                                                    uu____65613)
                                                             with
                                                             | ((b',uu____65639),
                                                                (b,uu____65641))
                                                                 ->
                                                                 let uu____65662
                                                                   =
                                                                   let uu____65669
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    b  in
                                                                   (b',
                                                                    uu____65669)
                                                                    in
                                                                 FStar_Syntax_Syntax.NT
                                                                   uu____65662)
                                                        bs_params bs1
                                                       in
                                                    let t3 =
                                                      let uu____65675 =
                                                        let uu____65676 =
                                                          FStar_Syntax_Syntax.mk_Total
                                                            body
                                                           in
                                                        FStar_Syntax_Util.arrow
                                                          rest uu____65676
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____65675
                                                        (FStar_Syntax_Subst.subst
                                                           subst1)
                                                       in
                                                    [{ dname = d; dtyp = t3 }]))
                                      | uu____65679 -> []))
                               in
                            let metadata =
                              let uu____65683 =
                                extract_metadata
                                  (FStar_List.append
                                     se.FStar_Syntax_Syntax.sigattrs attrs)
                                 in
                              let uu____65686 =
                                FStar_List.choose flag_of_qual quals  in
                              FStar_List.append uu____65683 uu____65686  in
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
                   | uu____65693 -> (env1, [])) env ses
             in
          match uu____65384 with
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
    let uu___820_65873 = empty_iface  in
    {
      iface_module_name = (uu___820_65873.iface_module_name);
      iface_bindings = fvs;
      iface_tydefs = (uu___820_65873.iface_tydefs);
      iface_type_names = (uu___820_65873.iface_type_names)
    }
  
let (iface_of_tydefs : FStar_Extraction_ML_UEnv.tydef Prims.list -> iface) =
  fun tds  ->
    let uu___823_65884 = empty_iface  in
    let uu____65885 =
      FStar_List.map (fun td  -> td.FStar_Extraction_ML_UEnv.tydef_fv) tds
       in
    {
      iface_module_name = (uu___823_65884.iface_module_name);
      iface_bindings = (uu___823_65884.iface_bindings);
      iface_tydefs = tds;
      iface_type_names = uu____65885
    }
  
let (iface_of_type_names : FStar_Syntax_Syntax.fv Prims.list -> iface) =
  fun fvs  ->
    let uu___827_65900 = empty_iface  in
    {
      iface_module_name = (uu___827_65900.iface_module_name);
      iface_bindings = (uu___827_65900.iface_bindings);
      iface_tydefs = (uu___827_65900.iface_tydefs);
      iface_type_names = fvs
    }
  
let (iface_union : iface -> iface -> iface) =
  fun if1  ->
    fun if2  ->
      let uu____65912 =
        if if1.iface_module_name <> if1.iface_module_name
        then failwith "Union not defined"
        else if1.iface_module_name  in
      {
        iface_module_name = uu____65912;
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
  'Auu____65957 .
    FStar_Extraction_ML_Syntax.mlpath ->
      ('Auu____65957 * FStar_Extraction_ML_Syntax.mlty) -> Prims.string
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
      let uu____65989 =
        FStar_Extraction_ML_Code.string_of_mlexpr cm
          e.FStar_Extraction_ML_UEnv.exp_b_expr
         in
      let uu____65991 =
        tscheme_to_string cm e.FStar_Extraction_ML_UEnv.exp_b_tscheme  in
      let uu____65993 =
        FStar_Util.string_of_bool e.FStar_Extraction_ML_UEnv.exp_b_inst_ok
         in
      FStar_Util.format4
        "{\n\texp_b_name = %s\n\texp_b_expr = %s\n\texp_b_tscheme = %s\n\texp_b_is_rec = %s }"
        e.FStar_Extraction_ML_UEnv.exp_b_name uu____65989 uu____65991
        uu____65993
  
let (print_binding :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_UEnv.exp_binding) ->
      Prims.string)
  =
  fun cm  ->
    fun uu____66011  ->
      match uu____66011 with
      | (fv,exp_binding) ->
          let uu____66019 = FStar_Syntax_Print.fv_to_string fv  in
          let uu____66021 = print_exp_binding cm exp_binding  in
          FStar_Util.format2 "(%s, %s)" uu____66019 uu____66021
  
let (print_tydef :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_UEnv.tydef -> Prims.string)
  =
  fun cm  ->
    fun tydef  ->
      let uu____66036 =
        FStar_Syntax_Print.fv_to_string
          tydef.FStar_Extraction_ML_UEnv.tydef_fv
         in
      let uu____66038 =
        tscheme_to_string cm tydef.FStar_Extraction_ML_UEnv.tydef_def  in
      FStar_Util.format2 "(%s, %s)" uu____66036 uu____66038
  
let (iface_to_string : iface -> Prims.string) =
  fun iface1  ->
    let cm = iface1.iface_module_name  in
    let print_type_name tn = FStar_Syntax_Print.fv_to_string tn  in
    let uu____66056 =
      let uu____66058 =
        FStar_List.map (print_binding cm) iface1.iface_bindings  in
      FStar_All.pipe_right uu____66058 (FStar_String.concat "\n")  in
    let uu____66072 =
      let uu____66074 = FStar_List.map (print_tydef cm) iface1.iface_tydefs
         in
      FStar_All.pipe_right uu____66074 (FStar_String.concat "\n")  in
    let uu____66084 =
      let uu____66086 =
        FStar_List.map print_type_name iface1.iface_type_names  in
      FStar_All.pipe_right uu____66086 (FStar_String.concat "\n")  in
    FStar_Util.format4
      "Interface %s = {\niface_bindings=\n%s;\n\niface_tydefs=\n%s;\n\niface_type_names=%s;\n}"
      (mlpath_to_string iface1.iface_module_name) uu____66056 uu____66072
      uu____66084
  
let (gamma_to_string : FStar_Extraction_ML_UEnv.uenv -> Prims.string) =
  fun env  ->
    let cm = env.FStar_Extraction_ML_UEnv.currentModule  in
    let gamma =
      FStar_List.collect
        (fun uu___614_66119  ->
           match uu___614_66119 with
           | FStar_Extraction_ML_UEnv.Fv (b,e) -> [(b, e)]
           | uu____66136 -> []) env.FStar_Extraction_ML_UEnv.env_bindings
       in
    let uu____66141 =
      let uu____66143 = FStar_List.map (print_binding cm) gamma  in
      FStar_All.pipe_right uu____66143 (FStar_String.concat "\n")  in
    FStar_Util.format1 "Gamma = {\n %s }" uu____66141
  
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
          let uu____66203 =
            let uu____66212 =
              FStar_TypeChecker_Env.open_universes_in
                env.FStar_Extraction_ML_UEnv.env_tcenv
                lb.FStar_Syntax_Syntax.lbunivs
                [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp]
               in
            match uu____66212 with
            | (tcenv,uu____66230,def_typ) ->
                let uu____66236 = as_pair def_typ  in (tcenv, uu____66236)
             in
          match uu____66203 with
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
                let uu____66267 =
                  let uu____66268 = FStar_Syntax_Subst.compress lbdef1  in
                  FStar_All.pipe_right uu____66268 FStar_Syntax_Util.unmeta
                   in
                FStar_All.pipe_right uu____66267 FStar_Syntax_Util.un_uinst
                 in
              let def1 =
                match def.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_abs uu____66276 ->
                    FStar_Extraction_ML_Term.normalize_abs def
                | uu____66295 -> def  in
              let uu____66296 =
                match def1.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____66307) ->
                    FStar_Syntax_Subst.open_term bs body
                | uu____66332 -> ([], def1)  in
              (match uu____66296 with
               | (bs,body) ->
                   let assumed =
                     FStar_Util.for_some
                       (fun uu___615_66352  ->
                          match uu___615_66352 with
                          | FStar_Syntax_Syntax.Assumption  -> true
                          | uu____66355 -> false) quals
                      in
                   let uu____66357 = binders_as_mlty_binders env bs  in
                   (match uu____66357 with
                    | (env1,ml_bs) ->
                        let body1 =
                          let uu____66384 =
                            FStar_Extraction_ML_Term.term_as_mlty env1 body
                             in
                          FStar_All.pipe_right uu____66384
                            (FStar_Extraction_ML_Util.eraseTypeDeep
                               (FStar_Extraction_ML_Util.udelta_unfold env1))
                           in
                        let mangled_projector =
                          let uu____66389 =
                            FStar_All.pipe_right quals
                              (FStar_Util.for_some
                                 (fun uu___616_66396  ->
                                    match uu___616_66396 with
                                    | FStar_Syntax_Syntax.Projector
                                        uu____66398 -> true
                                    | uu____66404 -> false))
                             in
                          if uu____66389
                          then
                            let mname = mangle_projector_lid lid  in
                            FStar_Pervasives_Native.Some
                              ((mname.FStar_Ident.ident).FStar_Ident.idText)
                          else FStar_Pervasives_Native.None  in
                        let metadata =
                          let uu____66418 = extract_metadata attrs  in
                          let uu____66421 =
                            FStar_List.choose flag_of_qual quals  in
                          FStar_List.append uu____66418 uu____66421  in
                        let td =
                          let uu____66444 = lident_as_mlsymbol lid  in
                          (assumed, uu____66444, mangled_projector, ml_bs,
                            metadata,
                            (FStar_Pervasives_Native.Some
                               (FStar_Extraction_ML_Syntax.MLTD_Abbrev body1)))
                           in
                        let def2 =
                          let uu____66456 =
                            let uu____66457 =
                              let uu____66458 = FStar_Ident.range_of_lid lid
                                 in
                              FStar_Extraction_ML_Util.mlloc_of_range
                                uu____66458
                               in
                            FStar_Extraction_ML_Syntax.MLM_Loc uu____66457
                             in
                          [uu____66456;
                          FStar_Extraction_ML_Syntax.MLM_Ty [td]]  in
                        let uu____66459 =
                          let uu____66464 =
                            FStar_All.pipe_right quals
                              (FStar_Util.for_some
                                 (fun uu___617_66470  ->
                                    match uu___617_66470 with
                                    | FStar_Syntax_Syntax.Assumption  -> true
                                    | FStar_Syntax_Syntax.New  -> true
                                    | uu____66474 -> false))
                             in
                          if uu____66464
                          then
                            let uu____66481 =
                              FStar_Extraction_ML_UEnv.extend_type_name env
                                fv
                               in
                            (uu____66481, (iface_of_type_names [fv]))
                          else
                            (let uu____66484 =
                               FStar_Extraction_ML_UEnv.extend_tydef env fv
                                 td
                                in
                             match uu____66484 with
                             | (env2,tydef) ->
                                 let uu____66495 = iface_of_tydefs [tydef]
                                    in
                                 (env2, uu____66495))
                           in
                        (match uu____66459 with
                         | (env2,iface1) -> (env2, iface1, def2))))
  
let (extract_bundle_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt -> (env_t * iface))
  =
  fun env  ->
    fun se  ->
      let extract_ctor env_iparams ml_tyvars env1 ctor =
        let mlt =
          let uu____66571 =
            FStar_Extraction_ML_Term.term_as_mlty env_iparams ctor.dtyp  in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env_iparams) uu____66571
           in
        let tys = (ml_tyvars, mlt)  in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp  in
        let uu____66578 =
          FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false  in
        match uu____66578 with | (env2,uu____66597,b) -> (env2, (fvv, b))  in
      let extract_one_family env1 ind =
        let uu____66636 = binders_as_mlty_binders env1 ind.iparams  in
        match uu____66636 with
        | (env_iparams,vars) ->
            let uu____66664 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor env_iparams vars) env1)
               in
            (match uu____66664 with | (env2,ctors) -> (env2, ctors))
         in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____66728,t,uu____66730,uu____66731,uu____66732);
            FStar_Syntax_Syntax.sigrng = uu____66733;
            FStar_Syntax_Syntax.sigquals = uu____66734;
            FStar_Syntax_Syntax.sigmeta = uu____66735;
            FStar_Syntax_Syntax.sigattrs = uu____66736;_}::[],uu____66737),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____66756 = extract_ctor env [] env { dname = l; dtyp = t }
             in
          (match uu____66756 with
           | (env1,ctor) -> (env1, (iface_of_bindings [ctor])))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____66789),quals) ->
          let uu____66803 =
            bundle_as_inductive_families env ses quals
              se.FStar_Syntax_Syntax.sigattrs
             in
          (match uu____66803 with
           | (env1,ifams) ->
               let uu____66820 =
                 FStar_Util.fold_map extract_one_family env1 ifams  in
               (match uu____66820 with
                | (env2,td) ->
                    let uu____66861 =
                      let uu____66862 =
                        let uu____66863 =
                          FStar_List.map (fun x  -> x.ifv) ifams  in
                        iface_of_type_names uu____66863  in
                      iface_union uu____66862
                        (iface_of_bindings (FStar_List.flatten td))
                       in
                    (env2, uu____66861)))
      | uu____66872 -> failwith "Unexpected signature element"
  
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
              let uu____66947 =
                let uu____66949 =
                  FStar_All.pipe_right quals
                    (FStar_Util.for_some
                       (fun uu___618_66955  ->
                          match uu___618_66955 with
                          | FStar_Syntax_Syntax.Assumption  -> true
                          | uu____66958 -> false))
                   in
                Prims.op_Negation uu____66949  in
              if uu____66947
              then (g, empty_iface, [])
              else
                (let uu____66973 = FStar_Syntax_Util.arrow_formals t  in
                 match uu____66973 with
                 | (bs,uu____66997) ->
                     let fv =
                       FStar_Syntax_Syntax.lid_as_fv lid
                         FStar_Syntax_Syntax.delta_constant
                         FStar_Pervasives_Native.None
                        in
                     let lb =
                       let uu____67020 =
                         FStar_Syntax_Util.abs bs FStar_Syntax_Syntax.t_unit
                           FStar_Pervasives_Native.None
                          in
                       {
                         FStar_Syntax_Syntax.lbname = (FStar_Util.Inr fv);
                         FStar_Syntax_Syntax.lbunivs = univs1;
                         FStar_Syntax_Syntax.lbtyp = t;
                         FStar_Syntax_Syntax.lbeff =
                           FStar_Parser_Const.effect_Tot_lid;
                         FStar_Syntax_Syntax.lbdef = uu____67020;
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
        let uu____67083 =
          FStar_Extraction_ML_UEnv.extend_fv' g1 fv ml_name tysc false false
           in
        match uu____67083 with
        | (g2,mangled_name,exp_binding) ->
            ((let uu____67105 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g2.FStar_Extraction_ML_UEnv.env_tcenv)
                  (FStar_Options.Other "ExtractionReify")
                 in
              if uu____67105
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
        (let uu____67141 =
           FStar_All.pipe_left
             (FStar_TypeChecker_Env.debug
                g.FStar_Extraction_ML_UEnv.env_tcenv)
             (FStar_Options.Other "ExtractionReify")
            in
         if uu____67141
         then
           let uu____67146 = FStar_Syntax_Print.term_to_string tm  in
           FStar_Util.print1 "extract_fv term: %s\n" uu____67146
         else ());
        (let uu____67151 =
           let uu____67152 = FStar_Syntax_Subst.compress tm  in
           uu____67152.FStar_Syntax_Syntax.n  in
         match uu____67151 with
         | FStar_Syntax_Syntax.Tm_uinst (tm1,uu____67160) -> extract_fv tm1
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             let mlp =
               FStar_Extraction_ML_Syntax.mlpath_of_lident
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             let uu____67167 = FStar_Extraction_ML_UEnv.lookup_fv g fv  in
             (match uu____67167 with
              | { FStar_Extraction_ML_UEnv.exp_b_name = uu____67172;
                  FStar_Extraction_ML_UEnv.exp_b_expr = uu____67173;
                  FStar_Extraction_ML_UEnv.exp_b_tscheme = tysc;
                  FStar_Extraction_ML_UEnv.exp_b_inst_ok = uu____67175;_} ->
                  let uu____67178 =
                    FStar_All.pipe_left
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.MLTY_Top)
                      (FStar_Extraction_ML_Syntax.MLE_Name mlp)
                     in
                  (uu____67178, tysc))
         | uu____67179 ->
             let uu____67180 =
               let uu____67182 =
                 FStar_Range.string_of_range tm.FStar_Syntax_Syntax.pos  in
               let uu____67184 = FStar_Syntax_Print.term_to_string tm  in
               FStar_Util.format2 "(%s) Not an fv: %s" uu____67182
                 uu____67184
                in
             failwith uu____67180)
         in
      let extract_action g1 a =
        (let uu____67212 =
           FStar_All.pipe_left
             (FStar_TypeChecker_Env.debug
                g1.FStar_Extraction_ML_UEnv.env_tcenv)
             (FStar_Options.Other "ExtractionReify")
            in
         if uu____67212
         then
           let uu____67217 =
             FStar_Syntax_Print.term_to_string
               a.FStar_Syntax_Syntax.action_typ
              in
           let uu____67219 =
             FStar_Syntax_Print.term_to_string
               a.FStar_Syntax_Syntax.action_defn
              in
           FStar_Util.print2 "Action type %s and term %s\n" uu____67217
             uu____67219
         else ());
        (let uu____67224 = FStar_Extraction_ML_UEnv.action_name ed a  in
         match uu____67224 with
         | (a_nm,a_lid) ->
             let lbname =
               let uu____67244 =
                 FStar_Syntax_Syntax.new_bv
                   (FStar_Pervasives_Native.Some
                      ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                   FStar_Syntax_Syntax.tun
                  in
               FStar_Util.Inl uu____67244  in
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
             let uu____67274 =
               FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb  in
             (match uu____67274 with
              | (a_let,uu____67290,ty) ->
                  ((let uu____67293 =
                      FStar_All.pipe_left
                        (FStar_TypeChecker_Env.debug
                           g1.FStar_Extraction_ML_UEnv.env_tcenv)
                        (FStar_Options.Other "ExtractionReify")
                       in
                    if uu____67293
                    then
                      let uu____67298 =
                        FStar_Extraction_ML_Code.string_of_mlexpr a_nm a_let
                         in
                      FStar_Util.print1 "Extracted action term: %s\n"
                        uu____67298
                    else ());
                   (let uu____67303 =
                      match a_let.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Let
                          ((uu____67326,mllb::[]),uu____67328) ->
                          (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc
                           with
                           | FStar_Pervasives_Native.Some tysc ->
                               ((mllb.FStar_Extraction_ML_Syntax.mllb_def),
                                 tysc)
                           | FStar_Pervasives_Native.None  ->
                               failwith "No type scheme")
                      | uu____67368 -> failwith "Impossible"  in
                    match uu____67303 with
                    | (exp,tysc) ->
                        ((let uu____67406 =
                            FStar_All.pipe_left
                              (FStar_TypeChecker_Env.debug
                                 g1.FStar_Extraction_ML_UEnv.env_tcenv)
                              (FStar_Options.Other "ExtractionReify")
                             in
                          if uu____67406
                          then
                            ((let uu____67412 =
                                FStar_Extraction_ML_Code.string_of_mlty a_nm
                                  (FStar_Pervasives_Native.snd tysc)
                                 in
                              FStar_Util.print1 "Extracted action type: %s\n"
                                uu____67412);
                             FStar_List.iter
                               (fun x  ->
                                  FStar_Util.print1 "and binders: %s\n" x)
                               (FStar_Pervasives_Native.fst tysc))
                          else ());
                         (let uu____67428 = extend_env g1 a_lid a_nm exp tysc
                             in
                          match uu____67428 with
                          | (env,iface1,impl) -> (env, (iface1, impl))))))))
         in
      let uu____67450 =
        let uu____67457 =
          extract_fv
            (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.return_repr)
           in
        match uu____67457 with
        | (return_tm,ty_sc) ->
            let uu____67474 =
              FStar_Extraction_ML_UEnv.monad_op_name ed "return"  in
            (match uu____67474 with
             | (return_nm,return_lid) ->
                 extend_env g return_lid return_nm return_tm ty_sc)
         in
      match uu____67450 with
      | (g1,return_iface,return_decl) ->
          let uu____67499 =
            let uu____67506 =
              extract_fv
                (FStar_Pervasives_Native.snd ed.FStar_Syntax_Syntax.bind_repr)
               in
            match uu____67506 with
            | (bind_tm,ty_sc) ->
                let uu____67523 =
                  FStar_Extraction_ML_UEnv.monad_op_name ed "bind"  in
                (match uu____67523 with
                 | (bind_nm,bind_lid) ->
                     extend_env g1 bind_lid bind_nm bind_tm ty_sc)
             in
          (match uu____67499 with
           | (g2,bind_iface,bind_decl) ->
               let uu____67548 =
                 FStar_Util.fold_map extract_action g2
                   ed.FStar_Syntax_Syntax.actions
                  in
               (match uu____67548 with
                | (g3,actions) ->
                    let uu____67585 = FStar_List.unzip actions  in
                    (match uu____67585 with
                     | (actions_iface,actions1) ->
                         let uu____67612 =
                           iface_union_l (return_iface :: bind_iface ::
                             actions_iface)
                            in
                         (g3, uu____67612, (return_decl :: bind_decl ::
                           actions1)))))
  
let (extract_sigelt_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle uu____67634 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____67643 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_datacon uu____67660 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) when
          FStar_Extraction_ML_Term.is_arity g t ->
          let uu____67679 =
            extract_type_declaration g lid se.FStar_Syntax_Syntax.sigquals
              se.FStar_Syntax_Syntax.sigattrs univs1 t
             in
          (match uu____67679 with | (env,iface1,uu____67694) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____67700) when
          FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp ->
          let uu____67709 =
            extract_typ_abbrev g se.FStar_Syntax_Syntax.sigquals
              se.FStar_Syntax_Syntax.sigattrs lb
             in
          (match uu____67709 with | (env,iface1,uu____67724) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,_univs,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let uu____67735 =
            (FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption))
              &&
              (let uu____67741 =
                 FStar_TypeChecker_Util.must_erase_for_extraction
                   g.FStar_Extraction_ML_UEnv.env_tcenv t
                  in
               Prims.op_Negation uu____67741)
             in
          if uu____67735
          then
            let uu____67748 =
              let uu____67759 =
                let uu____67760 =
                  let uu____67763 = always_fail lid t  in [uu____67763]  in
                (false, uu____67760)  in
              FStar_Extraction_ML_Term.extract_lb_iface g uu____67759  in
            (match uu____67748 with
             | (g1,bindings) -> (g1, (iface_of_bindings bindings)))
          else (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____67789) ->
          let uu____67794 = FStar_Extraction_ML_Term.extract_lb_iface g lbs
             in
          (match uu____67794 with
           | (g1,bindings) -> (g1, (iface_of_bindings bindings)))
      | FStar_Syntax_Syntax.Sig_main uu____67823 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____67824 ->
          (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_assume uu____67825 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____67832 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____67833 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          (FStar_Syntax_Util.process_pragma p se.FStar_Syntax_Syntax.sigrng;
           (g, empty_iface))
      | FStar_Syntax_Syntax.Sig_splice uu____67848 ->
          failwith "impossible: trying to extract splice"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____67861 =
            (FStar_TypeChecker_Env.is_reifiable_effect
               g.FStar_Extraction_ML_UEnv.env_tcenv
               ed.FStar_Syntax_Syntax.mname)
              && (FStar_List.isEmpty ed.FStar_Syntax_Syntax.binders)
             in
          if uu____67861
          then
            let uu____67874 = extract_reifiable_effect g ed  in
            (match uu____67874 with
             | (env,iface1,uu____67889) -> (env, iface1))
          else (g, empty_iface)
  
let (extract_iface' :
  env_t ->
    FStar_Syntax_Syntax.modul -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun modul  ->
      let uu____67911 = FStar_Options.interactive ()  in
      if uu____67911
      then (g, empty_iface)
      else
        (let uu____67920 = FStar_Options.restore_cmd_line_options true  in
         let decls = modul.FStar_Syntax_Syntax.declarations  in
         let iface1 =
           let uu___1166_67924 = empty_iface  in
           {
             iface_module_name = (g.FStar_Extraction_ML_UEnv.currentModule);
             iface_bindings = (uu___1166_67924.iface_bindings);
             iface_tydefs = (uu___1166_67924.iface_tydefs);
             iface_type_names = (uu___1166_67924.iface_type_names)
           }  in
         let res =
           FStar_List.fold_left
             (fun uu____67942  ->
                fun se  ->
                  match uu____67942 with
                  | (g1,iface2) ->
                      let uu____67954 = extract_sigelt_iface g1 se  in
                      (match uu____67954 with
                       | (g2,iface') ->
                           let uu____67965 = iface_union iface2 iface'  in
                           (g2, uu____67965))) (g, iface1) decls
            in
         (let uu____67967 = FStar_Options.restore_cmd_line_options true  in
          FStar_All.pipe_left (fun a1  -> ()) uu____67967);
         res)
  
let (extract_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.modul -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g  ->
    fun modul  ->
      let uu____67984 = FStar_Options.debug_any ()  in
      if uu____67984
      then
        let uu____67991 =
          FStar_Util.format1 "Extracted interface of %s"
            (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
           in
        FStar_Util.measure_execution_time uu____67991
          (fun uu____67999  -> extract_iface' g modul)
      else extract_iface' g modul
  
let (extend_with_iface :
  FStar_Extraction_ML_UEnv.uenv -> iface -> FStar_Extraction_ML_UEnv.uenv) =
  fun g  ->
    fun iface1  ->
      let uu___1184_68013 = g  in
      let uu____68014 =
        let uu____68017 =
          FStar_List.map (fun _68024  -> FStar_Extraction_ML_UEnv.Fv _68024)
            iface1.iface_bindings
           in
        FStar_List.append uu____68017 g.FStar_Extraction_ML_UEnv.env_bindings
         in
      {
        FStar_Extraction_ML_UEnv.env_tcenv =
          (uu___1184_68013.FStar_Extraction_ML_UEnv.env_tcenv);
        FStar_Extraction_ML_UEnv.env_bindings = uu____68014;
        FStar_Extraction_ML_UEnv.tydefs =
          (FStar_List.append iface1.iface_tydefs
             g.FStar_Extraction_ML_UEnv.tydefs);
        FStar_Extraction_ML_UEnv.type_names =
          (FStar_List.append iface1.iface_type_names
             g.FStar_Extraction_ML_UEnv.type_names);
        FStar_Extraction_ML_UEnv.currentModule =
          (uu___1184_68013.FStar_Extraction_ML_UEnv.currentModule)
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
          let uu____68102 =
            FStar_Extraction_ML_Term.term_as_mlty env_iparams ctor.dtyp  in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env_iparams) uu____68102
           in
        let steps =
          [FStar_TypeChecker_Env.Inlining;
          FStar_TypeChecker_Env.UnfoldUntil
            FStar_Syntax_Syntax.delta_constant;
          FStar_TypeChecker_Env.EraseUniverses;
          FStar_TypeChecker_Env.AllowUnboundUniverses]  in
        let names1 =
          let uu____68110 =
            let uu____68111 =
              let uu____68114 =
                FStar_TypeChecker_Normalize.normalize steps
                  env_iparams.FStar_Extraction_ML_UEnv.env_tcenv ctor.dtyp
                 in
              FStar_Syntax_Subst.compress uu____68114  in
            uu____68111.FStar_Syntax_Syntax.n  in
          match uu____68110 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,uu____68119) ->
              FStar_List.map
                (fun uu____68152  ->
                   match uu____68152 with
                   | ({ FStar_Syntax_Syntax.ppname = ppname;
                        FStar_Syntax_Syntax.index = uu____68161;
                        FStar_Syntax_Syntax.sort = uu____68162;_},uu____68163)
                       -> ppname.FStar_Ident.idText) bs
          | uu____68171 -> []  in
        let tys = (ml_tyvars, mlt)  in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp  in
        let uu____68179 =
          FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false  in
        match uu____68179 with
        | (env2,uu____68206,uu____68207) ->
            let uu____68210 =
              let uu____68223 = lident_as_mlsymbol ctor.dname  in
              let uu____68225 =
                let uu____68233 = FStar_Extraction_ML_Util.argTypes mlt  in
                FStar_List.zip names1 uu____68233  in
              (uu____68223, uu____68225)  in
            (env2, uu____68210)
         in
      let extract_one_family env1 ind =
        let uu____68294 = binders_as_mlty_binders env1 ind.iparams  in
        match uu____68294 with
        | (env_iparams,vars) ->
            let uu____68338 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor env_iparams vars) env1)
               in
            (match uu____68338 with
             | (env2,ctors) ->
                 let uu____68445 = FStar_Syntax_Util.arrow_formals ind.ityp
                    in
                 (match uu____68445 with
                  | (indices,uu____68487) ->
                      let ml_params =
                        let uu____68512 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____68538  ->
                                    let uu____68546 =
                                      FStar_Util.string_of_int i  in
                                    Prims.op_Hat "'dummyV" uu____68546))
                           in
                        FStar_List.append vars uu____68512  in
                      let tbody =
                        let uu____68551 =
                          FStar_Util.find_opt
                            (fun uu___619_68556  ->
                               match uu___619_68556 with
                               | FStar_Syntax_Syntax.RecordType uu____68558
                                   -> true
                               | uu____68568 -> false) ind.iquals
                           in
                        match uu____68551 with
                        | FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                            let uu____68580 = FStar_List.hd ctors  in
                            (match uu____68580 with
                             | (uu____68605,c_ty) ->
                                 let fields =
                                   FStar_List.map2
                                     (fun id1  ->
                                        fun uu____68649  ->
                                          match uu____68649 with
                                          | (uu____68660,ty) ->
                                              let lid =
                                                FStar_Ident.lid_of_ids
                                                  (FStar_List.append ns [id1])
                                                 in
                                              let uu____68665 =
                                                lident_as_mlsymbol lid  in
                                              (uu____68665, ty)) ids c_ty
                                    in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____68668 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors
                         in
                      let uu____68671 =
                        let uu____68694 = lident_as_mlsymbol ind.iname  in
                        (false, uu____68694, FStar_Pervasives_Native.None,
                          ml_params, (ind.imetadata),
                          (FStar_Pervasives_Native.Some tbody))
                         in
                      (env2, uu____68671)))
         in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____68739,t,uu____68741,uu____68742,uu____68743);
            FStar_Syntax_Syntax.sigrng = uu____68744;
            FStar_Syntax_Syntax.sigquals = uu____68745;
            FStar_Syntax_Syntax.sigmeta = uu____68746;
            FStar_Syntax_Syntax.sigattrs = uu____68747;_}::[],uu____68748),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____68767 = extract_ctor env [] env { dname = l; dtyp = t }
             in
          (match uu____68767 with
           | (env1,ctor) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____68820),quals) ->
          let uu____68834 =
            bundle_as_inductive_families env ses quals
              se.FStar_Syntax_Syntax.sigattrs
             in
          (match uu____68834 with
           | (env1,ifams) ->
               let uu____68853 =
                 FStar_Util.fold_map extract_one_family env1 ifams  in
               (match uu____68853 with
                | (env2,td) -> (env2, [FStar_Extraction_ML_Syntax.MLM_Ty td])))
      | uu____68962 -> failwith "Unexpected signature element"
  
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
             let uu____69020 = FStar_Syntax_Util.head_and_args t  in
             match uu____69020 with
             | (head1,args) ->
                 let uu____69068 =
                   let uu____69070 =
                     FStar_Syntax_Util.is_fvar FStar_Parser_Const.plugin_attr
                       head1
                      in
                   Prims.op_Negation uu____69070  in
                 if uu____69068
                 then FStar_Pervasives_Native.None
                 else
                   (match args with
                    | ({
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_int (s,uu____69089));
                         FStar_Syntax_Syntax.pos = uu____69090;
                         FStar_Syntax_Syntax.vars = uu____69091;_},uu____69092)::[]
                        ->
                        let uu____69131 =
                          let uu____69135 = FStar_Util.int_of_string s  in
                          FStar_Pervasives_Native.Some uu____69135  in
                        FStar_Pervasives_Native.Some uu____69131
                    | uu____69141 ->
                        FStar_Pervasives_Native.Some
                          FStar_Pervasives_Native.None))
         in
      let uu____69156 =
        let uu____69158 = FStar_Options.codegen ()  in
        uu____69158 <> (FStar_Pervasives_Native.Some FStar_Options.Plugin)
         in
      if uu____69156
      then []
      else
        (let uu____69168 = plugin_with_arity se.FStar_Syntax_Syntax.sigattrs
            in
         match uu____69168 with
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
                      let uu____69210 =
                        let uu____69211 = FStar_Ident.string_of_lid fv_lid1
                           in
                        FStar_Extraction_ML_Syntax.MLC_String uu____69211  in
                      FStar_Extraction_ML_Syntax.MLE_Const uu____69210  in
                    let uu____69213 =
                      FStar_Extraction_ML_Util.interpret_plugin_as_term_fun
                        g.FStar_Extraction_ML_UEnv.env_tcenv fv fv_t
                        arity_opt ml_name_str
                       in
                    match uu____69213 with
                    | FStar_Pervasives_Native.Some
                        (interp,nbe_interp,arity,plugin1) ->
                        let uu____69246 =
                          if plugin1
                          then
                            ("FStar_Tactics_Native.register_plugin",
                              [interp; nbe_interp])
                          else
                            ("FStar_Tactics_Native.register_tactic",
                              [interp])
                           in
                        (match uu____69246 with
                         | (register,args) ->
                             let h =
                               let uu____69283 =
                                 let uu____69284 =
                                   let uu____69285 =
                                     FStar_Ident.lid_of_str register  in
                                   FStar_Extraction_ML_Syntax.mlpath_of_lident
                                     uu____69285
                                    in
                                 FStar_Extraction_ML_Syntax.MLE_Name
                                   uu____69284
                                  in
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    FStar_Extraction_ML_Syntax.MLTY_Top)
                                 uu____69283
                                in
                             let arity1 =
                               let uu____69287 =
                                 let uu____69288 =
                                   let uu____69300 =
                                     FStar_Util.string_of_int arity  in
                                   (uu____69300,
                                     FStar_Pervasives_Native.None)
                                    in
                                 FStar_Extraction_ML_Syntax.MLC_Int
                                   uu____69288
                                  in
                               FStar_Extraction_ML_Syntax.MLE_Const
                                 uu____69287
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
              | uu____69329 -> []))
  
let rec (extract_sig :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list))
  =
  fun g  ->
    fun se  ->
      FStar_Extraction_ML_UEnv.debug g
        (fun u  ->
           let uu____69357 = FStar_Syntax_Print.sigelt_to_string se  in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____69357);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle uu____69366 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____69375 ->
           extract_bundle g se
       | FStar_Syntax_Syntax.Sig_datacon uu____69392 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           FStar_TypeChecker_Env.is_reifiable_effect
             g.FStar_Extraction_ML_UEnv.env_tcenv
             ed.FStar_Syntax_Syntax.mname
           ->
           let uu____69409 = extract_reifiable_effect g ed  in
           (match uu____69409 with | (env,_iface,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_splice uu____69433 ->
           failwith "impossible: trying to extract splice"
       | FStar_Syntax_Syntax.Sig_new_effect uu____69447 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,univs1,t) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let uu____69453 =
             extract_type_declaration g lid se.FStar_Syntax_Syntax.sigquals
               se.FStar_Syntax_Syntax.sigattrs univs1 t
              in
           (match uu____69453 with | (env,uu____69469,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____69478) when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let uu____69487 =
             extract_typ_abbrev g se.FStar_Syntax_Syntax.sigquals
               se.FStar_Syntax_Syntax.sigattrs lb
              in
           (match uu____69487 with | (env,uu____69503,impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____69512) ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs  in
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____69523 =
             let uu____69532 =
               FStar_Syntax_Util.extract_attr'
                 FStar_Parser_Const.postprocess_extr_with attrs
                in
             match uu____69532 with
             | FStar_Pervasives_Native.None  ->
                 (attrs, FStar_Pervasives_Native.None)
             | FStar_Pervasives_Native.Some
                 (ats,(tau,FStar_Pervasives_Native.None )::uu____69561) ->
                 (ats, (FStar_Pervasives_Native.Some tau))
             | FStar_Pervasives_Native.Some (ats,args) ->
                 (FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng
                    (FStar_Errors.Warning_UnrecognizedAttribute,
                      "Ill-formed application of `postprocess_for_extraction_with`");
                  (attrs, FStar_Pervasives_Native.None))
              in
           (match uu____69523 with
            | (attrs1,post_tau) ->
                let postprocess_lb tau lb =
                  let lbdef =
                    FStar_TypeChecker_Env.postprocess
                      g.FStar_Extraction_ML_UEnv.env_tcenv tau
                      lb.FStar_Syntax_Syntax.lbtyp
                      lb.FStar_Syntax_Syntax.lbdef
                     in
                  let uu___1403_69647 = lb  in
                  {
                    FStar_Syntax_Syntax.lbname =
                      (uu___1403_69647.FStar_Syntax_Syntax.lbname);
                    FStar_Syntax_Syntax.lbunivs =
                      (uu___1403_69647.FStar_Syntax_Syntax.lbunivs);
                    FStar_Syntax_Syntax.lbtyp =
                      (uu___1403_69647.FStar_Syntax_Syntax.lbtyp);
                    FStar_Syntax_Syntax.lbeff =
                      (uu___1403_69647.FStar_Syntax_Syntax.lbeff);
                    FStar_Syntax_Syntax.lbdef = lbdef;
                    FStar_Syntax_Syntax.lbattrs =
                      (uu___1403_69647.FStar_Syntax_Syntax.lbattrs);
                    FStar_Syntax_Syntax.lbpos =
                      (uu___1403_69647.FStar_Syntax_Syntax.lbpos)
                  }  in
                let lbs1 =
                  let uu____69656 =
                    match post_tau with
                    | FStar_Pervasives_Native.Some tau ->
                        FStar_List.map (postprocess_lb tau)
                          (FStar_Pervasives_Native.snd lbs)
                    | FStar_Pervasives_Native.None  ->
                        FStar_Pervasives_Native.snd lbs
                     in
                  ((FStar_Pervasives_Native.fst lbs), uu____69656)  in
                let uu____69674 =
                  let uu____69681 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_let
                         (lbs1, FStar_Syntax_Util.exp_false_bool))
                      FStar_Pervasives_Native.None
                      se.FStar_Syntax_Syntax.sigrng
                     in
                  FStar_Extraction_ML_Term.term_as_mlexpr g uu____69681  in
                (match uu____69674 with
                 | (ml_let,uu____69698,uu____69699) ->
                     (match ml_let.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Let
                          ((flavor,bindings),uu____69708) ->
                          let flags = FStar_List.choose flag_of_qual quals
                             in
                          let flags' = extract_metadata attrs1  in
                          let uu____69725 =
                            FStar_List.fold_left2
                              (fun uu____69751  ->
                                 fun ml_lb  ->
                                   fun uu____69753  ->
                                     match (uu____69751, uu____69753) with
                                     | ((env,ml_lbs),{
                                                       FStar_Syntax_Syntax.lbname
                                                         = lbname;
                                                       FStar_Syntax_Syntax.lbunivs
                                                         = uu____69775;
                                                       FStar_Syntax_Syntax.lbtyp
                                                         = t;
                                                       FStar_Syntax_Syntax.lbeff
                                                         = uu____69777;
                                                       FStar_Syntax_Syntax.lbdef
                                                         = uu____69778;
                                                       FStar_Syntax_Syntax.lbattrs
                                                         = uu____69779;
                                                       FStar_Syntax_Syntax.lbpos
                                                         = uu____69780;_})
                                         ->
                                         let uu____69805 =
                                           FStar_All.pipe_right
                                             ml_lb.FStar_Extraction_ML_Syntax.mllb_meta
                                             (FStar_List.contains
                                                FStar_Extraction_ML_Syntax.Erased)
                                            in
                                         if uu____69805
                                         then (env, ml_lbs)
                                         else
                                           (let lb_lid =
                                              let uu____69822 =
                                                let uu____69825 =
                                                  FStar_Util.right lbname  in
                                                uu____69825.FStar_Syntax_Syntax.fv_name
                                                 in
                                              uu____69822.FStar_Syntax_Syntax.v
                                               in
                                            let flags'' =
                                              let uu____69829 =
                                                let uu____69830 =
                                                  FStar_Syntax_Subst.compress
                                                    t
                                                   in
                                                uu____69830.FStar_Syntax_Syntax.n
                                                 in
                                              match uu____69829 with
                                              | FStar_Syntax_Syntax.Tm_arrow
                                                  (uu____69835,{
                                                                 FStar_Syntax_Syntax.n
                                                                   =
                                                                   FStar_Syntax_Syntax.Comp
                                                                   {
                                                                    FStar_Syntax_Syntax.comp_univs
                                                                    =
                                                                    uu____69836;
                                                                    FStar_Syntax_Syntax.effect_name
                                                                    = e;
                                                                    FStar_Syntax_Syntax.result_typ
                                                                    =
                                                                    uu____69838;
                                                                    FStar_Syntax_Syntax.effect_args
                                                                    =
                                                                    uu____69839;
                                                                    FStar_Syntax_Syntax.flags
                                                                    =
                                                                    uu____69840;_};
                                                                 FStar_Syntax_Syntax.pos
                                                                   =
                                                                   uu____69841;
                                                                 FStar_Syntax_Syntax.vars
                                                                   =
                                                                   uu____69842;_})
                                                  when
                                                  let uu____69877 =
                                                    FStar_Ident.string_of_lid
                                                      e
                                                     in
                                                  uu____69877 =
                                                    "FStar.HyperStack.ST.StackInline"
                                                  ->
                                                  [FStar_Extraction_ML_Syntax.StackInline]
                                              | uu____69881 -> []  in
                                            let meta =
                                              FStar_List.append flags
                                                (FStar_List.append flags'
                                                   flags'')
                                               in
                                            let ml_lb1 =
                                              let uu___1451_69886 = ml_lb  in
                                              {
                                                FStar_Extraction_ML_Syntax.mllb_name
                                                  =
                                                  (uu___1451_69886.FStar_Extraction_ML_Syntax.mllb_name);
                                                FStar_Extraction_ML_Syntax.mllb_tysc
                                                  =
                                                  (uu___1451_69886.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                FStar_Extraction_ML_Syntax.mllb_add_unit
                                                  =
                                                  (uu___1451_69886.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                FStar_Extraction_ML_Syntax.mllb_def
                                                  =
                                                  (uu___1451_69886.FStar_Extraction_ML_Syntax.mllb_def);
                                                FStar_Extraction_ML_Syntax.mllb_meta
                                                  = meta;
                                                FStar_Extraction_ML_Syntax.print_typ
                                                  =
                                                  (uu___1451_69886.FStar_Extraction_ML_Syntax.print_typ)
                                              }  in
                                            let uu____69887 =
                                              let uu____69892 =
                                                FStar_All.pipe_right quals
                                                  (FStar_Util.for_some
                                                     (fun uu___620_69899  ->
                                                        match uu___620_69899
                                                        with
                                                        | FStar_Syntax_Syntax.Projector
                                                            uu____69901 ->
                                                            true
                                                        | uu____69907 ->
                                                            false))
                                                 in
                                              if uu____69892
                                              then
                                                let mname =
                                                  let uu____69923 =
                                                    mangle_projector_lid
                                                      lb_lid
                                                     in
                                                  FStar_All.pipe_right
                                                    uu____69923
                                                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                                                   in
                                                let uu____69932 =
                                                  let uu____69940 =
                                                    FStar_Util.right lbname
                                                     in
                                                  let uu____69941 =
                                                    FStar_Util.must
                                                      ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc
                                                     in
                                                  FStar_Extraction_ML_UEnv.extend_fv'
                                                    env uu____69940 mname
                                                    uu____69941
                                                    ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                                    false
                                                   in
                                                match uu____69932 with
                                                | (env1,uu____69948,uu____69949)
                                                    ->
                                                    (env1,
                                                      (let uu___1464_69953 =
                                                         ml_lb1  in
                                                       {
                                                         FStar_Extraction_ML_Syntax.mllb_name
                                                           =
                                                           (FStar_Pervasives_Native.snd
                                                              mname);
                                                         FStar_Extraction_ML_Syntax.mllb_tysc
                                                           =
                                                           (uu___1464_69953.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                         FStar_Extraction_ML_Syntax.mllb_add_unit
                                                           =
                                                           (uu___1464_69953.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                         FStar_Extraction_ML_Syntax.mllb_def
                                                           =
                                                           (uu___1464_69953.FStar_Extraction_ML_Syntax.mllb_def);
                                                         FStar_Extraction_ML_Syntax.mllb_meta
                                                           =
                                                           (uu___1464_69953.FStar_Extraction_ML_Syntax.mllb_meta);
                                                         FStar_Extraction_ML_Syntax.print_typ
                                                           =
                                                           (uu___1464_69953.FStar_Extraction_ML_Syntax.print_typ)
                                                       }))
                                              else
                                                (let uu____69960 =
                                                   let uu____69968 =
                                                     FStar_Util.must
                                                       ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc
                                                      in
                                                   FStar_Extraction_ML_UEnv.extend_lb
                                                     env lbname t uu____69968
                                                     ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit
                                                     false
                                                    in
                                                 match uu____69960 with
                                                 | (env1,uu____69975,uu____69976)
                                                     -> (env1, ml_lb1))
                                               in
                                            match uu____69887 with
                                            | (g1,ml_lb2) ->
                                                (g1, (ml_lb2 :: ml_lbs))))
                              (g, []) bindings
                              (FStar_Pervasives_Native.snd lbs1)
                             in
                          (match uu____69725 with
                           | (g1,ml_lbs') ->
                               let uu____70006 =
                                 let uu____70009 =
                                   let uu____70012 =
                                     let uu____70013 =
                                       FStar_Extraction_ML_Util.mlloc_of_range
                                         se.FStar_Syntax_Syntax.sigrng
                                        in
                                     FStar_Extraction_ML_Syntax.MLM_Loc
                                       uu____70013
                                      in
                                   [uu____70012;
                                   FStar_Extraction_ML_Syntax.MLM_Let
                                     (flavor, (FStar_List.rev ml_lbs'))]
                                    in
                                 let uu____70016 =
                                   maybe_register_plugin g1 se  in
                                 FStar_List.append uu____70009 uu____70016
                                  in
                               (g1, uu____70006))
                      | uu____70021 ->
                          let uu____70022 =
                            let uu____70024 =
                              FStar_Extraction_ML_Code.string_of_mlexpr
                                g.FStar_Extraction_ML_UEnv.currentModule
                                ml_let
                               in
                            FStar_Util.format1
                              "Impossible: Translated a let to a non-let: %s"
                              uu____70024
                             in
                          failwith uu____70022)))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____70034,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals  in
           let uu____70039 =
             (FStar_All.pipe_right quals
                (FStar_List.contains FStar_Syntax_Syntax.Assumption))
               &&
               (let uu____70045 =
                  FStar_TypeChecker_Util.must_erase_for_extraction
                    g.FStar_Extraction_ML_UEnv.env_tcenv t
                   in
                Prims.op_Negation uu____70045)
              in
           if uu____70039
           then
             let always_fail1 =
               let uu___1484_70055 = se  in
               let uu____70056 =
                 let uu____70057 =
                   let uu____70064 =
                     let uu____70065 =
                       let uu____70068 = always_fail lid t  in [uu____70068]
                        in
                     (false, uu____70065)  in
                   (uu____70064, [])  in
                 FStar_Syntax_Syntax.Sig_let uu____70057  in
               {
                 FStar_Syntax_Syntax.sigel = uu____70056;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___1484_70055.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___1484_70055.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___1484_70055.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___1484_70055.FStar_Syntax_Syntax.sigattrs)
               }  in
             let uu____70075 = extract_sig g always_fail1  in
             (match uu____70075 with
              | (g1,mlm) ->
                  let uu____70094 =
                    FStar_Util.find_map quals
                      (fun uu___621_70099  ->
                         match uu___621_70099 with
                         | FStar_Syntax_Syntax.Discriminator l ->
                             FStar_Pervasives_Native.Some l
                         | uu____70103 -> FStar_Pervasives_Native.None)
                     in
                  (match uu____70094 with
                   | FStar_Pervasives_Native.Some l ->
                       let uu____70111 =
                         let uu____70114 =
                           let uu____70115 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng
                              in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____70115  in
                         let uu____70116 =
                           let uu____70119 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l
                              in
                           [uu____70119]  in
                         uu____70114 :: uu____70116  in
                       (g1, uu____70111)
                   | uu____70122 ->
                       let uu____70125 =
                         FStar_Util.find_map quals
                           (fun uu___622_70131  ->
                              match uu___622_70131 with
                              | FStar_Syntax_Syntax.Projector (l,uu____70135)
                                  -> FStar_Pervasives_Native.Some l
                              | uu____70136 -> FStar_Pervasives_Native.None)
                          in
                       (match uu____70125 with
                        | FStar_Pervasives_Native.Some uu____70143 ->
                            (g1, [])
                        | uu____70146 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____70156 = FStar_Extraction_ML_Term.term_as_mlexpr g e  in
           (match uu____70156 with
            | (ml_main,uu____70170,uu____70171) ->
                let uu____70172 =
                  let uu____70175 =
                    let uu____70176 =
                      FStar_Extraction_ML_Util.mlloc_of_range
                        se.FStar_Syntax_Syntax.sigrng
                       in
                    FStar_Extraction_ML_Syntax.MLM_Loc uu____70176  in
                  [uu____70175; FStar_Extraction_ML_Syntax.MLM_Top ml_main]
                   in
                (g, uu____70172))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____70179 ->
           failwith "impossible -- removed by tc.fs"
       | FStar_Syntax_Syntax.Sig_assume uu____70187 -> (g, [])
       | FStar_Syntax_Syntax.Sig_sub_effect uu____70196 -> (g, [])
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____70199 -> (g, [])
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
      let uu____70241 = FStar_Options.restore_cmd_line_options true  in
      let name =
        FStar_Extraction_ML_Syntax.mlpath_of_lident
          m.FStar_Syntax_Syntax.name
         in
      let g1 =
        let uu___1527_70245 = g  in
        let uu____70246 =
          FStar_TypeChecker_Env.set_current_module
            g.FStar_Extraction_ML_UEnv.env_tcenv m.FStar_Syntax_Syntax.name
           in
        {
          FStar_Extraction_ML_UEnv.env_tcenv = uu____70246;
          FStar_Extraction_ML_UEnv.env_bindings =
            (uu___1527_70245.FStar_Extraction_ML_UEnv.env_bindings);
          FStar_Extraction_ML_UEnv.tydefs =
            (uu___1527_70245.FStar_Extraction_ML_UEnv.tydefs);
          FStar_Extraction_ML_UEnv.type_names =
            (uu___1527_70245.FStar_Extraction_ML_UEnv.type_names);
          FStar_Extraction_ML_UEnv.currentModule = name
        }  in
      let uu____70247 =
        FStar_Util.fold_map
          (fun g2  ->
             fun se  ->
               let uu____70266 =
                 FStar_Options.debug_module
                   (m.FStar_Syntax_Syntax.name).FStar_Ident.str
                  in
               if uu____70266
               then
                 let nm =
                   let uu____70277 =
                     FStar_All.pipe_right
                       (FStar_Syntax_Util.lids_of_sigelt se)
                       (FStar_List.map FStar_Ident.string_of_lid)
                      in
                   FStar_All.pipe_right uu____70277
                     (FStar_String.concat ", ")
                    in
                 (FStar_Util.print1 "+++About to extract {%s}\n" nm;
                  (let uu____70294 =
                     FStar_Util.format1 "---Extracted {%s}" nm  in
                   FStar_Util.measure_execution_time uu____70294
                     (fun uu____70304  -> extract_sig g2 se)))
               else extract_sig g2 se) g1 m.FStar_Syntax_Syntax.declarations
         in
      match uu____70247 with
      | (g2,sigs) ->
          let mlm = FStar_List.flatten sigs  in
          let is_kremlin =
            let uu____70326 = FStar_Options.codegen ()  in
            uu____70326 =
              (FStar_Pervasives_Native.Some FStar_Options.Kremlin)
             in
          if
            ((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims") &&
              (is_kremlin ||
                 (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface))
          then
            ((let uu____70341 =
                let uu____70343 = FStar_Options.silent ()  in
                Prims.op_Negation uu____70343  in
              if uu____70341
              then
                let uu____70346 =
                  FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
                FStar_Util.print1 "Extracted module %s\n" uu____70346
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
      (let uu____70421 = FStar_Options.restore_cmd_line_options true  in
       FStar_All.pipe_left (fun a2  -> ()) uu____70421);
      (let uu____70424 =
         let uu____70426 =
           FStar_Options.should_extract
             (m.FStar_Syntax_Syntax.name).FStar_Ident.str
            in
         Prims.op_Negation uu____70426  in
       if uu____70424
       then
         let uu____70429 =
           let uu____70431 =
             FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name  in
           FStar_Util.format1
             "Extract called on a module %s that should not be extracted"
             uu____70431
            in
         failwith uu____70429
       else ());
      (let uu____70436 = FStar_Options.interactive ()  in
       if uu____70436
       then (g, FStar_Pervasives_Native.None)
       else
         (let res =
            let uu____70456 = FStar_Options.debug_any ()  in
            if uu____70456
            then
              let msg =
                let uu____70467 =
                  FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name
                   in
                FStar_Util.format1 "Extracting module %s\n" uu____70467  in
              FStar_Util.measure_execution_time msg
                (fun uu____70477  -> extract' g m)
            else extract' g m  in
          (let uu____70481 = FStar_Options.restore_cmd_line_options true  in
           FStar_All.pipe_left (fun a3  -> ()) uu____70481);
          res))
  
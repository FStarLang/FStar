open Prims
type ty_binding =
  {
  ty_b_name: FStar_Extraction_ML_Syntax.mlident ;
  ty_b_ty: FStar_Extraction_ML_Syntax.mlty }
let (__proj__Mkty_binding__item__ty_b_name :
  ty_binding -> FStar_Extraction_ML_Syntax.mlident) =
  fun projectee  ->
    match projectee with | { ty_b_name; ty_b_ty;_} -> ty_b_name
  
let (__proj__Mkty_binding__item__ty_b_ty :
  ty_binding -> FStar_Extraction_ML_Syntax.mlty) =
  fun projectee  -> match projectee with | { ty_b_name; ty_b_ty;_} -> ty_b_ty 
type exp_binding =
  {
  exp_b_name: FStar_Extraction_ML_Syntax.mlident ;
  exp_b_expr: FStar_Extraction_ML_Syntax.mlexpr ;
  exp_b_tscheme: FStar_Extraction_ML_Syntax.mltyscheme ;
  exp_b_inst_ok: Prims.bool }
let (__proj__Mkexp_binding__item__exp_b_name :
  exp_binding -> FStar_Extraction_ML_Syntax.mlident) =
  fun projectee  ->
    match projectee with
    | { exp_b_name; exp_b_expr; exp_b_tscheme; exp_b_inst_ok;_} -> exp_b_name
  
let (__proj__Mkexp_binding__item__exp_b_expr :
  exp_binding -> FStar_Extraction_ML_Syntax.mlexpr) =
  fun projectee  ->
    match projectee with
    | { exp_b_name; exp_b_expr; exp_b_tscheme; exp_b_inst_ok;_} -> exp_b_expr
  
let (__proj__Mkexp_binding__item__exp_b_tscheme :
  exp_binding -> FStar_Extraction_ML_Syntax.mltyscheme) =
  fun projectee  ->
    match projectee with
    | { exp_b_name; exp_b_expr; exp_b_tscheme; exp_b_inst_ok;_} ->
        exp_b_tscheme
  
let (__proj__Mkexp_binding__item__exp_b_inst_ok : exp_binding -> Prims.bool)
  =
  fun projectee  ->
    match projectee with
    | { exp_b_name; exp_b_expr; exp_b_tscheme; exp_b_inst_ok;_} ->
        exp_b_inst_ok
  
type ty_or_exp_b = (ty_binding,exp_binding) FStar_Util.either
type binding =
  | Bv of (FStar_Syntax_Syntax.bv * ty_or_exp_b) 
  | Fv of (FStar_Syntax_Syntax.fv * exp_binding) 
let (uu___is_Bv : binding -> Prims.bool) =
  fun projectee  -> match projectee with | Bv _0 -> true | uu____160 -> false 
let (__proj__Bv__item___0 :
  binding -> (FStar_Syntax_Syntax.bv * ty_or_exp_b)) =
  fun projectee  -> match projectee with | Bv _0 -> _0 
let (uu___is_Fv : binding -> Prims.bool) =
  fun projectee  -> match projectee with | Fv _0 -> true | uu____195 -> false 
let (__proj__Fv__item___0 :
  binding -> (FStar_Syntax_Syntax.fv * exp_binding)) =
  fun projectee  -> match projectee with | Fv _0 -> _0 
type tydef =
  {
  tydef_fv: FStar_Syntax_Syntax.fv ;
  tydef_mlmodule_name: FStar_Extraction_ML_Syntax.mlsymbol Prims.list ;
  tydef_name: FStar_Extraction_ML_Syntax.mlsymbol ;
  tydef_mangled_name:
    FStar_Extraction_ML_Syntax.mlsymbol FStar_Pervasives_Native.option ;
  tydef_def: FStar_Extraction_ML_Syntax.mltyscheme }
let (__proj__Mktydef__item__tydef_fv : tydef -> FStar_Syntax_Syntax.fv) =
  fun projectee  ->
    match projectee with
    | { tydef_fv; tydef_mlmodule_name; tydef_name; tydef_mangled_name;
        tydef_def;_} -> tydef_fv
  
let (__proj__Mktydef__item__tydef_mlmodule_name :
  tydef -> FStar_Extraction_ML_Syntax.mlsymbol Prims.list) =
  fun projectee  ->
    match projectee with
    | { tydef_fv; tydef_mlmodule_name; tydef_name; tydef_mangled_name;
        tydef_def;_} -> tydef_mlmodule_name
  
let (__proj__Mktydef__item__tydef_name :
  tydef -> FStar_Extraction_ML_Syntax.mlsymbol) =
  fun projectee  ->
    match projectee with
    | { tydef_fv; tydef_mlmodule_name; tydef_name; tydef_mangled_name;
        tydef_def;_} -> tydef_name
  
let (__proj__Mktydef__item__tydef_mangled_name :
  tydef -> FStar_Extraction_ML_Syntax.mlsymbol FStar_Pervasives_Native.option)
  =
  fun projectee  ->
    match projectee with
    | { tydef_fv; tydef_mlmodule_name; tydef_name; tydef_mangled_name;
        tydef_def;_} -> tydef_mangled_name
  
let (__proj__Mktydef__item__tydef_def :
  tydef -> FStar_Extraction_ML_Syntax.mltyscheme) =
  fun projectee  ->
    match projectee with
    | { tydef_fv; tydef_mlmodule_name; tydef_name; tydef_mangled_name;
        tydef_def;_} -> tydef_def
  
let (tydef_fv : tydef -> FStar_Syntax_Syntax.fv) = fun td  -> td.tydef_fv 
let (tydef_def : tydef -> FStar_Extraction_ML_Syntax.mltyscheme) =
  fun td  -> td.tydef_def 
let (tydef_mlpath : tydef -> FStar_Extraction_ML_Syntax.mlpath) =
  fun td  -> ((td.tydef_mlmodule_name), (td.tydef_name)) 
type uenv =
  {
  env_tcenv: FStar_TypeChecker_Env.env ;
  env_bindings: binding Prims.list ;
  env_mlident_map: FStar_Extraction_ML_Syntax.mlident FStar_Util.psmap ;
  mlpath_of_lid: FStar_Extraction_ML_Syntax.mlpath FStar_Util.psmap ;
  env_fieldname_map: FStar_Extraction_ML_Syntax.mlident FStar_Util.psmap ;
  mlpath_of_fieldname: FStar_Extraction_ML_Syntax.mlpath FStar_Util.psmap ;
  tydefs: tydef Prims.list ;
  type_names:
    (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_Syntax.mlpath) Prims.list ;
  currentModule: FStar_Extraction_ML_Syntax.mlpath }
let (__proj__Mkuenv__item__env_tcenv : uenv -> FStar_TypeChecker_Env.env) =
  fun projectee  ->
    match projectee with
    | { env_tcenv; env_bindings; env_mlident_map; mlpath_of_lid;
        env_fieldname_map; mlpath_of_fieldname; tydefs; type_names;
        currentModule;_} -> env_tcenv
  
let (__proj__Mkuenv__item__env_bindings : uenv -> binding Prims.list) =
  fun projectee  ->
    match projectee with
    | { env_tcenv; env_bindings; env_mlident_map; mlpath_of_lid;
        env_fieldname_map; mlpath_of_fieldname; tydefs; type_names;
        currentModule;_} -> env_bindings
  
let (__proj__Mkuenv__item__env_mlident_map :
  uenv -> FStar_Extraction_ML_Syntax.mlident FStar_Util.psmap) =
  fun projectee  ->
    match projectee with
    | { env_tcenv; env_bindings; env_mlident_map; mlpath_of_lid;
        env_fieldname_map; mlpath_of_fieldname; tydefs; type_names;
        currentModule;_} -> env_mlident_map
  
let (__proj__Mkuenv__item__mlpath_of_lid :
  uenv -> FStar_Extraction_ML_Syntax.mlpath FStar_Util.psmap) =
  fun projectee  ->
    match projectee with
    | { env_tcenv; env_bindings; env_mlident_map; mlpath_of_lid;
        env_fieldname_map; mlpath_of_fieldname; tydefs; type_names;
        currentModule;_} -> mlpath_of_lid
  
let (__proj__Mkuenv__item__env_fieldname_map :
  uenv -> FStar_Extraction_ML_Syntax.mlident FStar_Util.psmap) =
  fun projectee  ->
    match projectee with
    | { env_tcenv; env_bindings; env_mlident_map; mlpath_of_lid;
        env_fieldname_map; mlpath_of_fieldname; tydefs; type_names;
        currentModule;_} -> env_fieldname_map
  
let (__proj__Mkuenv__item__mlpath_of_fieldname :
  uenv -> FStar_Extraction_ML_Syntax.mlpath FStar_Util.psmap) =
  fun projectee  ->
    match projectee with
    | { env_tcenv; env_bindings; env_mlident_map; mlpath_of_lid;
        env_fieldname_map; mlpath_of_fieldname; tydefs; type_names;
        currentModule;_} -> mlpath_of_fieldname
  
let (__proj__Mkuenv__item__tydefs : uenv -> tydef Prims.list) =
  fun projectee  ->
    match projectee with
    | { env_tcenv; env_bindings; env_mlident_map; mlpath_of_lid;
        env_fieldname_map; mlpath_of_fieldname; tydefs; type_names;
        currentModule;_} -> tydefs
  
let (__proj__Mkuenv__item__type_names :
  uenv ->
    (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_Syntax.mlpath) Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { env_tcenv; env_bindings; env_mlident_map; mlpath_of_lid;
        env_fieldname_map; mlpath_of_fieldname; tydefs; type_names;
        currentModule;_} -> type_names
  
let (__proj__Mkuenv__item__currentModule :
  uenv -> FStar_Extraction_ML_Syntax.mlpath) =
  fun projectee  ->
    match projectee with
    | { env_tcenv; env_bindings; env_mlident_map; mlpath_of_lid;
        env_fieldname_map; mlpath_of_fieldname; tydefs; type_names;
        currentModule;_} -> currentModule
  
let (tcenv_of_uenv : uenv -> FStar_TypeChecker_Env.env) =
  fun u  -> u.env_tcenv 
let (set_tcenv : uenv -> FStar_TypeChecker_Env.env -> uenv) =
  fun u  ->
    fun t  ->
      let uu___73_811 = u  in
      {
        env_tcenv = t;
        env_bindings = (uu___73_811.env_bindings);
        env_mlident_map = (uu___73_811.env_mlident_map);
        mlpath_of_lid = (uu___73_811.mlpath_of_lid);
        env_fieldname_map = (uu___73_811.env_fieldname_map);
        mlpath_of_fieldname = (uu___73_811.mlpath_of_fieldname);
        tydefs = (uu___73_811.tydefs);
        type_names = (uu___73_811.type_names);
        currentModule = (uu___73_811.currentModule)
      }
  
let (current_module_of_uenv : uenv -> FStar_Extraction_ML_Syntax.mlpath) =
  fun u  -> u.currentModule 
let (set_current_module : uenv -> FStar_Extraction_ML_Syntax.mlpath -> uenv)
  =
  fun u  ->
    fun m  ->
      let uu___81_829 = u  in
      {
        env_tcenv = (uu___81_829.env_tcenv);
        env_bindings = (uu___81_829.env_bindings);
        env_mlident_map = (uu___81_829.env_mlident_map);
        mlpath_of_lid = (uu___81_829.mlpath_of_lid);
        env_fieldname_map = (uu___81_829.env_fieldname_map);
        mlpath_of_fieldname = (uu___81_829.mlpath_of_fieldname);
        tydefs = (uu___81_829.tydefs);
        type_names = (uu___81_829.type_names);
        currentModule = m
      }
  
let (bindings_of_uenv : uenv -> binding Prims.list) =
  fun u  -> u.env_bindings 
let (debug : uenv -> (unit -> unit) -> unit) =
  fun g  ->
    fun f  ->
      let c = FStar_Extraction_ML_Syntax.string_of_mlpath g.currentModule  in
      let uu____856 =
        FStar_Options.debug_at_level c (FStar_Options.Other "Extraction")  in
      if uu____856 then f () else ()
  
let (mkFvvar :
  FStar_Ident.lident -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.fv) =
  fun l  ->
    fun t  ->
      FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
        FStar_Pervasives_Native.None
  
let (erasedContent : FStar_Extraction_ML_Syntax.mlty) =
  FStar_Extraction_ML_Syntax.MLTY_Erased 
let (erasableTypeNoDelta : FStar_Extraction_ML_Syntax.mlty -> Prims.bool) =
  fun t  ->
    if t = FStar_Extraction_ML_Syntax.ml_unit_ty
    then true
    else
      (match t with
       | FStar_Extraction_ML_Syntax.MLTY_Named
           (uu____887,("FStar"::"Ghost"::[],"erased")) -> true
       | FStar_Extraction_ML_Syntax.MLTY_Named
           (uu____903,("FStar"::"Tactics"::"Effect"::[],"tactic")) ->
           let uu____920 = FStar_Options.codegen ()  in
           uu____920 <> (FStar_Pervasives_Native.Some FStar_Options.Plugin)
       | uu____925 -> false)
  
let (unknownType : FStar_Extraction_ML_Syntax.mlty) =
  FStar_Extraction_ML_Syntax.MLTY_Top 
let (convRange : FStar_Range.range -> Prims.int) = fun r  -> Prims.int_zero 
let (convIdent : FStar_Ident.ident -> FStar_Extraction_ML_Syntax.mlident) =
  fun id  -> id.FStar_Ident.idText 
let rec (lookup_ty_local :
  binding Prims.list ->
    FStar_Syntax_Syntax.bv -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun gamma  ->
    fun b  ->
      match gamma with
      | (Bv (b',FStar_Util.Inl ty_b))::tl ->
          if FStar_Syntax_Syntax.bv_eq b b'
          then ty_b.ty_b_ty
          else lookup_ty_local tl b
      | (Bv (b',FStar_Util.Inr uu____969))::tl ->
          if FStar_Syntax_Syntax.bv_eq b b'
          then
            failwith
              (Prims.op_Hat "Type/Expr clash: "
                 (b.FStar_Syntax_Syntax.ppname).FStar_Ident.idText)
          else lookup_ty_local tl b
      | uu____977::tl -> lookup_ty_local tl b
      | [] ->
          failwith
            (Prims.op_Hat "extraction: unbound type var "
               (b.FStar_Syntax_Syntax.ppname).FStar_Ident.idText)
  
let tyscheme_of_td :
  'uuuuuu993 'uuuuuu994 'uuuuuu995 'uuuuuu996 .
    ('uuuuuu993 * 'uuuuuu994 * 'uuuuuu995 *
      FStar_Extraction_ML_Syntax.mlidents * 'uuuuuu996 *
      FStar_Extraction_ML_Syntax.mltybody FStar_Pervasives_Native.option) ->
      FStar_Extraction_ML_Syntax.mltyscheme FStar_Pervasives_Native.option
  =
  fun uu____1017  ->
    match uu____1017 with
    | (uu____1032,uu____1033,uu____1034,vars,uu____1036,body_opt) ->
        (match body_opt with
         | FStar_Pervasives_Native.Some
             (FStar_Extraction_ML_Syntax.MLTD_Abbrev t) ->
             FStar_Pervasives_Native.Some (vars, t)
         | uu____1047 -> FStar_Pervasives_Native.None)
  
let (lookup_ty_const :
  uenv ->
    FStar_Extraction_ML_Syntax.mlpath ->
      FStar_Extraction_ML_Syntax.mltyscheme FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun uu____1062  ->
      match uu____1062 with
      | (module_name,ty_name) ->
          FStar_Util.find_map env.tydefs
            (fun tydef1  ->
               if
                 (ty_name = tydef1.tydef_name) &&
                   (module_name = tydef1.tydef_mlmodule_name)
               then FStar_Pervasives_Native.Some (tydef1.tydef_def)
               else FStar_Pervasives_Native.None)
  
let (module_name_of_fv : FStar_Syntax_Syntax.fv -> Prims.string Prims.list) =
  fun fv  ->
    FStar_All.pipe_right
      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ns
      (FStar_List.map (fun i  -> i.FStar_Ident.idText))
  
let (maybe_mangle_type_projector :
  uenv ->
    FStar_Syntax_Syntax.fv ->
      FStar_Extraction_ML_Syntax.mlpath FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun fv  ->
      let mname = module_name_of_fv fv  in
      let ty_name =
        (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText
         in
      FStar_Util.find_map env.tydefs
        (fun tydef1  ->
           if
             (tydef1.tydef_name = ty_name) &&
               (tydef1.tydef_mlmodule_name = mname)
           then
             match tydef1.tydef_mangled_name with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some (mname, ty_name)
             | FStar_Pervasives_Native.Some mangled ->
                 FStar_Pervasives_Native.Some (mname, mangled)
           else FStar_Pervasives_Native.None)
  
let (lookup_tyvar :
  uenv -> FStar_Syntax_Syntax.bv -> FStar_Extraction_ML_Syntax.mlty) =
  fun g  -> fun bt  -> lookup_ty_local g.env_bindings bt 
let (try_lookup_fv :
  uenv ->
    FStar_Syntax_Syntax.fv -> exp_binding FStar_Pervasives_Native.option)
  =
  fun g  ->
    fun fv  ->
      FStar_Util.find_map g.env_bindings
        (fun uu___0_1228  ->
           match uu___0_1228 with
           | Fv (fv',t) when FStar_Syntax_Syntax.fv_eq fv fv' ->
               FStar_Pervasives_Native.Some t
           | uu____1233 -> FStar_Pervasives_Native.None)
  
let (lookup_fv : uenv -> FStar_Syntax_Syntax.fv -> exp_binding) =
  fun g  ->
    fun fv  ->
      let uu____1245 = try_lookup_fv g fv  in
      match uu____1245 with
      | FStar_Pervasives_Native.None  ->
          let uu____1248 =
            let uu____1250 =
              FStar_Range.string_of_range
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.p
               in
            let uu____1252 =
              FStar_Syntax_Print.lid_to_string
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            FStar_Util.format2 "(%s) free Variable %s not found\n" uu____1250
              uu____1252
             in
          failwith uu____1248
      | FStar_Pervasives_Native.Some y -> y
  
let (lookup_bv : uenv -> FStar_Syntax_Syntax.bv -> ty_or_exp_b) =
  fun g  ->
    fun bv  ->
      let x =
        FStar_Util.find_map g.env_bindings
          (fun uu___1_1273  ->
             match uu___1_1273 with
             | Bv (bv',r) when FStar_Syntax_Syntax.bv_eq bv bv' ->
                 FStar_Pervasives_Native.Some r
             | uu____1278 -> FStar_Pervasives_Native.None)
         in
      match x with
      | FStar_Pervasives_Native.None  ->
          let uu____1279 =
            let uu____1281 =
              FStar_Range.string_of_range
                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange
               in
            let uu____1283 = FStar_Syntax_Print.bv_to_string bv  in
            FStar_Util.format2 "(%s) bound Variable %s not found\n"
              uu____1281 uu____1283
             in
          failwith uu____1279
      | FStar_Pervasives_Native.Some y -> y
  
let (lookup :
  uenv ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
      (ty_or_exp_b * FStar_Syntax_Syntax.fv_qual
        FStar_Pervasives_Native.option))
  =
  fun g  ->
    fun x  ->
      match x with
      | FStar_Util.Inl x1 ->
          let uu____1319 = lookup_bv g x1  in
          (uu____1319, FStar_Pervasives_Native.None)
      | FStar_Util.Inr x1 ->
          let uu____1323 =
            let uu____1324 = lookup_fv g x1  in FStar_Util.Inr uu____1324  in
          (uu____1323, (x1.FStar_Syntax_Syntax.fv_qual))
  
let (lookup_term :
  uenv ->
    FStar_Syntax_Syntax.term ->
      (ty_or_exp_b * FStar_Syntax_Syntax.fv_qual
        FStar_Pervasives_Native.option))
  =
  fun g  ->
    fun t  ->
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_name x -> lookup g (FStar_Util.Inl x)
      | FStar_Syntax_Syntax.Tm_fvar x -> lookup g (FStar_Util.Inr x)
      | uu____1352 -> failwith "Impossible: lookup_term for a non-name"
  
let (sanitize : Prims.string -> Prims.bool -> Prims.string) =
  fun s  ->
    fun is_type  ->
      let cs = FStar_String.list_of_string s  in
      let sanitize_typ uu____1389 =
        let valid_rest c = FStar_Util.is_letter_or_digit c  in
        let aux cs1 =
          FStar_List.map
            (fun x  ->
               let uu____1420 = valid_rest x  in
               if uu____1420 then x else 117) cs1
           in
        let uu____1427 =
          let uu____1429 = FStar_List.hd cs  in uu____1429 = 39  in
        if uu____1427
        then
          let uu____1438 = FStar_List.hd cs  in
          let uu____1441 =
            let uu____1445 = FStar_List.tail cs  in aux uu____1445  in
          uu____1438 :: uu____1441
        else (let uu____1453 = aux cs  in 39 :: uu____1453)  in
      let sanitize_term uu____1467 =
        let valid c =
          ((FStar_Util.is_letter_or_digit c) || (c = 95)) || (c = 39)  in
        let cs' =
          FStar_List.fold_right
            (fun c  ->
               fun cs1  ->
                 let uu____1498 =
                   let uu____1502 = valid c  in
                   if uu____1502 then [c] else [95; 95]  in
                 FStar_List.append uu____1498 cs1) cs []
           in
        match cs' with
        | c::cs1 when (FStar_Util.is_digit c) || (c = 39) -> 95 :: c :: cs1
        | uu____1534 -> cs  in
      let uu____1538 = if is_type then sanitize_typ () else sanitize_term ()
         in
      FStar_String.string_of_list uu____1538
  
let (bv_as_mlident :
  FStar_Syntax_Syntax.bv -> FStar_Extraction_ML_Syntax.mlident) =
  fun x  ->
    let uu____1556 =
      (FStar_Util.starts_with
         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
         FStar_Ident.reserved_prefix)
        || (FStar_Syntax_Syntax.is_null_bv x)
       in
    if uu____1556
    then
      let uu____1560 =
        let uu____1562 = FStar_Util.string_of_int x.FStar_Syntax_Syntax.index
           in
        Prims.op_Hat "_" uu____1562  in
      Prims.op_Hat (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
        uu____1560
    else (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
  
let (find_uniq :
  Prims.string FStar_Util.psmap ->
    Prims.string ->
      Prims.bool -> (Prims.string * Prims.string FStar_Util.psmap))
  =
  fun ml_ident_map  ->
    fun mlident  ->
      fun is_type  ->
        let rec aux i mlident1 =
          let target_mlident =
            if i = Prims.int_zero
            then mlident1
            else
              (let uu____1632 = FStar_Util.string_of_int i  in
               Prims.op_Hat mlident1 uu____1632)
             in
          let uu____1634 =
            FStar_Util.psmap_try_find ml_ident_map target_mlident  in
          match uu____1634 with
          | FStar_Pervasives_Native.Some x ->
              aux (i + Prims.int_one) mlident1
          | FStar_Pervasives_Native.None  ->
              let map = FStar_Util.psmap_add ml_ident_map target_mlident ""
                 in
              (target_mlident, map)
           in
        let mlident1 = sanitize mlident is_type  in
        if is_type
        then
          let uu____1673 =
            let uu____1682 = FStar_Util.substring_from mlident1 Prims.int_one
               in
            aux Prims.int_zero uu____1682  in
          match uu____1673 with | (nm,map) -> ((Prims.op_Hat "'" nm), map)
        else aux Prims.int_zero mlident1
  
let (mlns_of_lid : FStar_Ident.lident -> Prims.string Prims.list) =
  fun x  ->
    FStar_List.map (fun x1  -> x1.FStar_Ident.idText) x.FStar_Ident.ns
  
let (new_mlpath_of_lident :
  uenv -> FStar_Ident.lident -> (FStar_Extraction_ML_Syntax.mlpath * uenv)) =
  fun g  ->
    fun x  ->
      let uu____1743 =
        let uu____1748 =
          FStar_Ident.lid_equals x FStar_Parser_Const.failwith_lid  in
        if uu____1748
        then (([], ((x.FStar_Ident.ident).FStar_Ident.idText)), g)
        else
          (let uu____1762 =
             find_uniq g.env_mlident_map
               (x.FStar_Ident.ident).FStar_Ident.idText false
              in
           match uu____1762 with
           | (name,map) ->
               let g1 =
                 let uu___271_1787 = g  in
                 {
                   env_tcenv = (uu___271_1787.env_tcenv);
                   env_bindings = (uu___271_1787.env_bindings);
                   env_mlident_map = map;
                   mlpath_of_lid = (uu___271_1787.mlpath_of_lid);
                   env_fieldname_map = (uu___271_1787.env_fieldname_map);
                   mlpath_of_fieldname = (uu___271_1787.mlpath_of_fieldname);
                   tydefs = (uu___271_1787.tydefs);
                   type_names = (uu___271_1787.type_names);
                   currentModule = (uu___271_1787.currentModule)
                 }  in
               let uu____1788 =
                 let uu____1789 = mlns_of_lid x  in (uu____1789, name)  in
               (uu____1788, g1))
         in
      match uu____1743 with
      | (mlp,g1) ->
          let g2 =
            let uu___277_1804 = g1  in
            let uu____1805 =
              FStar_Util.psmap_add g1.mlpath_of_lid x.FStar_Ident.str mlp  in
            {
              env_tcenv = (uu___277_1804.env_tcenv);
              env_bindings = (uu___277_1804.env_bindings);
              env_mlident_map = (uu___277_1804.env_mlident_map);
              mlpath_of_lid = uu____1805;
              env_fieldname_map = (uu___277_1804.env_fieldname_map);
              mlpath_of_fieldname = (uu___277_1804.mlpath_of_fieldname);
              tydefs = (uu___277_1804.tydefs);
              type_names = (uu___277_1804.type_names);
              currentModule = (uu___277_1804.currentModule)
            }  in
          (mlp, g2)
  
let (print_mlpath_map : uenv -> Prims.string) =
  fun g  ->
    let string_of_mlpath mlp =
      Prims.op_Hat
        (FStar_String.concat "." (FStar_Pervasives_Native.fst mlp))
        (Prims.op_Hat "." (FStar_Pervasives_Native.snd mlp))
       in
    let entries =
      FStar_Util.psmap_fold g.mlpath_of_lid
        (fun key  ->
           fun value  ->
             fun entries  ->
               let uu____1866 =
                 FStar_Util.format2 "%s -> %s\n" key (string_of_mlpath value)
                  in
               uu____1866 :: entries) []
       in
    FStar_String.concat "\n" entries
  
let (mlpath_of_lident :
  uenv -> FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlpath) =
  fun g  ->
    fun x  ->
      let uu____1883 =
        FStar_Util.psmap_try_find g.mlpath_of_lid x.FStar_Ident.str  in
      match uu____1883 with
      | FStar_Pervasives_Native.None  ->
          (debug g
             (fun uu____1890  ->
                FStar_Util.print1 "Identifier not found: %s"
                  x.FStar_Ident.str;
                (let uu____1893 = print_mlpath_map g  in
                 FStar_Util.print1 "Env is \n%s\n" uu____1893));
           failwith (Prims.op_Hat "Identifier not found: " x.FStar_Ident.str))
      | FStar_Pervasives_Native.Some mlp -> mlp
  
let (extend_ty : uenv -> FStar_Syntax_Syntax.bv -> Prims.bool -> uenv) =
  fun g  ->
    fun a  ->
      fun map_to_top  ->
        let is_type = Prims.op_Negation map_to_top  in
        let uu____1918 =
          let uu____1927 = bv_as_mlident a  in
          find_uniq g.env_mlident_map uu____1927 is_type  in
        match uu____1918 with
        | (ml_a,mlident_map) ->
            let mapped_to =
              if map_to_top
              then FStar_Extraction_ML_Syntax.MLTY_Top
              else FStar_Extraction_ML_Syntax.MLTY_Var ml_a  in
            let gamma =
              (Bv
                 (a,
                   (FStar_Util.Inl { ty_b_name = ml_a; ty_b_ty = mapped_to })))
              :: (g.env_bindings)  in
            let tcenv = FStar_TypeChecker_Env.push_bv g.env_tcenv a  in
            let uu___309_1947 = g  in
            {
              env_tcenv = tcenv;
              env_bindings = gamma;
              env_mlident_map = mlident_map;
              mlpath_of_lid = (uu___309_1947.mlpath_of_lid);
              env_fieldname_map = (uu___309_1947.env_fieldname_map);
              mlpath_of_fieldname = (uu___309_1947.mlpath_of_fieldname);
              tydefs = (uu___309_1947.tydefs);
              type_names = (uu___309_1947.type_names);
              currentModule = (uu___309_1947.currentModule)
            }
  
let (lookup_ty : uenv -> FStar_Syntax_Syntax.bv -> ty_binding) =
  fun g  ->
    fun x  ->
      let uu____1959 = lookup_bv g x  in
      match uu____1959 with
      | FStar_Util.Inl ty -> ty
      | uu____1961 -> failwith "Expected a type name"
  
let (extend_bv :
  uenv ->
    FStar_Syntax_Syntax.bv ->
      FStar_Extraction_ML_Syntax.mltyscheme ->
        Prims.bool ->
          Prims.bool ->
            Prims.bool ->
              (uenv * FStar_Extraction_ML_Syntax.mlident * exp_binding))
  =
  fun g  ->
    fun x  ->
      fun t_x  ->
        fun add_unit  ->
          fun is_rec  ->
            fun mk_unit  ->
              let ml_ty =
                match t_x with
                | ([],t) -> t
                | uu____2017 -> FStar_Extraction_ML_Syntax.MLTY_Top  in
              let uu____2018 =
                let uu____2027 = bv_as_mlident x  in
                find_uniq g.env_mlident_map uu____2027 false  in
              match uu____2018 with
              | (mlident,mlident_map) ->
                  let mlx = FStar_Extraction_ML_Syntax.MLE_Var mlident  in
                  let mlx1 =
                    if mk_unit
                    then FStar_Extraction_ML_Syntax.ml_unit
                    else
                      if add_unit
                      then
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top)
                          (FStar_Extraction_ML_Syntax.MLE_App
                             ((FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.MLTY_Top mlx),
                               [FStar_Extraction_ML_Syntax.ml_unit]))
                      else FStar_Extraction_ML_Syntax.with_ty ml_ty mlx
                     in
                  let t_x1 =
                    if add_unit
                    then FStar_Extraction_ML_Syntax.pop_unit t_x
                    else t_x  in
                  let exp_binding1 =
                    {
                      exp_b_name = mlident;
                      exp_b_expr = mlx1;
                      exp_b_tscheme = t_x1;
                      exp_b_inst_ok = is_rec
                    }  in
                  let gamma = (Bv (x, (FStar_Util.Inr exp_binding1))) ::
                    (g.env_bindings)  in
                  let tcenv =
                    let uu____2066 = FStar_Syntax_Syntax.binders_of_list [x]
                       in
                    FStar_TypeChecker_Env.push_binders g.env_tcenv uu____2066
                     in
                  ((let uu___344_2069 = g  in
                    {
                      env_tcenv = tcenv;
                      env_bindings = gamma;
                      env_mlident_map = mlident_map;
                      mlpath_of_lid = (uu___344_2069.mlpath_of_lid);
                      env_fieldname_map = (uu___344_2069.env_fieldname_map);
                      mlpath_of_fieldname =
                        (uu___344_2069.mlpath_of_fieldname);
                      tydefs = (uu___344_2069.tydefs);
                      type_names = (uu___344_2069.type_names);
                      currentModule = (uu___344_2069.currentModule)
                    }), mlident, exp_binding1)
  
let (new_mlident : uenv -> (uenv * FStar_Extraction_ML_Syntax.mlident)) =
  fun g  ->
    let ml_ty = FStar_Extraction_ML_Syntax.MLTY_Top  in
    let x =
      FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
        FStar_Syntax_Syntax.tun
       in
    let uu____2088 =
      extend_bv g x ([], FStar_Extraction_ML_Syntax.MLTY_Top) false false
        false
       in
    match uu____2088 with | (g1,id,uu____2107) -> (g1, id)
  
let rec (mltyFvars :
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlident Prims.list)
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Var x -> [x]
    | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,f,t2) ->
        let uu____2130 = mltyFvars t1  in
        let uu____2134 = mltyFvars t2  in
        FStar_List.append uu____2130 uu____2134
    | FStar_Extraction_ML_Syntax.MLTY_Named (args,path) ->
        FStar_List.collect mltyFvars args
    | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
        FStar_List.collect mltyFvars ts
    | FStar_Extraction_ML_Syntax.MLTY_Top  -> []
    | FStar_Extraction_ML_Syntax.MLTY_Erased  -> []
  
let rec (subsetMlidents :
  FStar_Extraction_ML_Syntax.mlident Prims.list ->
    FStar_Extraction_ML_Syntax.mlident Prims.list -> Prims.bool)
  =
  fun la  ->
    fun lb  ->
      match la with
      | h::tla -> (FStar_List.contains h lb) && (subsetMlidents tla lb)
      | [] -> true
  
let (tySchemeIsClosed : FStar_Extraction_ML_Syntax.mltyscheme -> Prims.bool)
  =
  fun tys  ->
    let uu____2195 = mltyFvars (FStar_Pervasives_Native.snd tys)  in
    subsetMlidents uu____2195 (FStar_Pervasives_Native.fst tys)
  
let (extend_fv :
  uenv ->
    FStar_Syntax_Syntax.fv ->
      FStar_Extraction_ML_Syntax.mltyscheme ->
        Prims.bool ->
          Prims.bool ->
            (uenv * FStar_Extraction_ML_Syntax.mlident * exp_binding))
  =
  fun g  ->
    fun x  ->
      fun t_x  ->
        fun add_unit  ->
          fun is_rec  ->
            let uu____2243 = tySchemeIsClosed t_x  in
            if uu____2243
            then
              let ml_ty =
                match t_x with
                | ([],t) -> t
                | uu____2256 -> FStar_Extraction_ML_Syntax.MLTY_Top  in
              let uu____2257 =
                new_mlpath_of_lident g
                  (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              match uu____2257 with
              | (mlpath,g1) ->
                  let mlsymbol = FStar_Pervasives_Native.snd mlpath  in
                  let mly = FStar_Extraction_ML_Syntax.MLE_Name mlpath  in
                  let mly1 =
                    if add_unit
                    then
                      FStar_All.pipe_left
                        (FStar_Extraction_ML_Syntax.with_ty
                           FStar_Extraction_ML_Syntax.MLTY_Top)
                        (FStar_Extraction_ML_Syntax.MLE_App
                           ((FStar_Extraction_ML_Syntax.with_ty
                               FStar_Extraction_ML_Syntax.MLTY_Top mly),
                             [FStar_Extraction_ML_Syntax.ml_unit]))
                    else FStar_Extraction_ML_Syntax.with_ty ml_ty mly  in
                  let t_x1 =
                    if add_unit
                    then FStar_Extraction_ML_Syntax.pop_unit t_x
                    else t_x  in
                  let exp_binding1 =
                    {
                      exp_b_name = mlsymbol;
                      exp_b_expr = mly1;
                      exp_b_tscheme = t_x1;
                      exp_b_inst_ok = is_rec
                    }  in
                  let gamma = (Fv (x, exp_binding1)) :: (g1.env_bindings)  in
                  let mlident_map =
                    FStar_Util.psmap_add g1.env_mlident_map mlsymbol ""  in
                  ((let uu___405_2300 = g1  in
                    {
                      env_tcenv = (uu___405_2300.env_tcenv);
                      env_bindings = gamma;
                      env_mlident_map = mlident_map;
                      mlpath_of_lid = (uu___405_2300.mlpath_of_lid);
                      env_fieldname_map = (uu___405_2300.env_fieldname_map);
                      mlpath_of_fieldname =
                        (uu___405_2300.mlpath_of_fieldname);
                      tydefs = (uu___405_2300.tydefs);
                      type_names = (uu___405_2300.type_names);
                      currentModule = (uu___405_2300.currentModule)
                    }), mlsymbol, exp_binding1)
            else failwith "freevars found"
  
let (extend_lb :
  uenv ->
    FStar_Syntax_Syntax.lbname ->
      FStar_Syntax_Syntax.typ ->
        FStar_Extraction_ML_Syntax.mltyscheme ->
          Prims.bool ->
            Prims.bool ->
              (uenv * FStar_Extraction_ML_Syntax.mlident * exp_binding))
  =
  fun g  ->
    fun l  ->
      fun t  ->
        fun t_x  ->
          fun add_unit  ->
            fun is_rec  ->
              match l with
              | FStar_Util.Inl x -> extend_bv g x t_x add_unit is_rec false
              | FStar_Util.Inr f -> extend_fv g f t_x add_unit is_rec
  
let (extend_tydef :
  uenv ->
    FStar_Syntax_Syntax.fv ->
      FStar_Extraction_ML_Syntax.mltyscheme ->
        (tydef * FStar_Extraction_ML_Syntax.mlpath * uenv))
  =
  fun g  ->
    fun fv  ->
      fun ts  ->
        let uu____2391 =
          new_mlpath_of_lident g
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        match uu____2391 with
        | (name,g1) ->
            let tydef1 =
              {
                tydef_fv = fv;
                tydef_mlmodule_name = (FStar_Pervasives_Native.fst name);
                tydef_name = (FStar_Pervasives_Native.snd name);
                tydef_mangled_name = FStar_Pervasives_Native.None;
                tydef_def = ts
              }  in
            (tydef1, name,
              (let uu___433_2415 = g1  in
               {
                 env_tcenv = (uu___433_2415.env_tcenv);
                 env_bindings = (uu___433_2415.env_bindings);
                 env_mlident_map = (uu___433_2415.env_mlident_map);
                 mlpath_of_lid = (uu___433_2415.mlpath_of_lid);
                 env_fieldname_map = (uu___433_2415.env_fieldname_map);
                 mlpath_of_fieldname = (uu___433_2415.mlpath_of_fieldname);
                 tydefs = (tydef1 :: (g1.tydefs));
                 type_names = ((fv, name) :: (g1.type_names));
                 currentModule = (uu___433_2415.currentModule)
               }))
  
let (extend_type_name :
  uenv ->
    FStar_Syntax_Syntax.fv -> (FStar_Extraction_ML_Syntax.mlpath * uenv))
  =
  fun g  ->
    fun fv  ->
      let uu____2439 =
        new_mlpath_of_lident g
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      match uu____2439 with
      | (name,g1) ->
          (name,
            (let uu___442_2451 = g1  in
             {
               env_tcenv = (uu___442_2451.env_tcenv);
               env_bindings = (uu___442_2451.env_bindings);
               env_mlident_map = (uu___442_2451.env_mlident_map);
               mlpath_of_lid = (uu___442_2451.mlpath_of_lid);
               env_fieldname_map = (uu___442_2451.env_fieldname_map);
               mlpath_of_fieldname = (uu___442_2451.mlpath_of_fieldname);
               tydefs = (uu___442_2451.tydefs);
               type_names = ((fv, name) :: (g1.type_names));
               currentModule = (uu___442_2451.currentModule)
             }))
  
let (is_type_name : uenv -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun g  ->
    fun fv  ->
      FStar_All.pipe_right g.type_names
        (FStar_Util.for_some
           (fun uu____2482  ->
              match uu____2482 with
              | (x,uu____2489) -> FStar_Syntax_Syntax.fv_eq fv x))
  
let (is_fv_type : uenv -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun g  ->
    fun fv  ->
      (is_type_name g fv) ||
        (FStar_All.pipe_right g.tydefs
           (FStar_Util.for_some
              (fun tydef1  -> FStar_Syntax_Syntax.fv_eq fv tydef1.tydef_fv)))
  
let (emptyMlPath : FStar_Extraction_ML_Syntax.mlpath) = ([], "") 
let (initial_mlident_map : unit -> Prims.string FStar_Util.psmap) =
  let map = FStar_Util.mk_ref FStar_Pervasives_Native.None  in
  fun uu____2538  ->
    let uu____2539 = FStar_ST.op_Bang map  in
    match uu____2539 with
    | FStar_Pervasives_Native.Some m -> m
    | FStar_Pervasives_Native.None  ->
        let m =
          let uu____2591 =
            let uu____2595 =
              let uu____2597 = FStar_Options.codegen ()  in
              uu____2597 =
                (FStar_Pervasives_Native.Some FStar_Options.FSharp)
               in
            if uu____2595
            then FStar_Extraction_ML_Syntax.fsharpkeywords
            else FStar_Extraction_ML_Syntax.ocamlkeywords  in
          let uu____2608 = FStar_Util.psmap_empty ()  in
          FStar_List.fold_right
            (fun x  -> fun m  -> FStar_Util.psmap_add m x "") uu____2591
            uu____2608
           in
        (FStar_ST.op_Colon_Equals map (FStar_Pervasives_Native.Some m); m)
  
let (mkContext : FStar_TypeChecker_Env.env -> uenv) =
  fun e  ->
    let env =
      let uu____2667 = initial_mlident_map ()  in
      let uu____2671 = FStar_Util.psmap_empty ()  in
      let uu____2674 = initial_mlident_map ()  in
      let uu____2678 = FStar_Util.psmap_empty ()  in
      {
        env_tcenv = e;
        env_bindings = [];
        env_mlident_map = uu____2667;
        mlpath_of_lid = uu____2671;
        env_fieldname_map = uu____2674;
        mlpath_of_fieldname = uu____2678;
        tydefs = [];
        type_names = [];
        currentModule = emptyMlPath
      }  in
    let a = "'a"  in
    let failwith_ty =
      ([a],
        (FStar_Extraction_ML_Syntax.MLTY_Fun
           ((FStar_Extraction_ML_Syntax.MLTY_Named
               ([], (["Prims"], "string"))),
             FStar_Extraction_ML_Syntax.E_IMPURE,
             (FStar_Extraction_ML_Syntax.MLTY_Var a))))
       in
    let uu____2705 =
      let uu____2713 =
        let uu____2714 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.failwith_lid
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        FStar_Util.Inr uu____2714  in
      extend_lb env uu____2713 FStar_Syntax_Syntax.tun failwith_ty false
        false
       in
    match uu____2705 with | (g,uu____2718,uu____2719) -> g
  
let (extend_with_monad_op_name :
  uenv ->
    FStar_Syntax_Syntax.eff_decl ->
      Prims.string ->
        FStar_Extraction_ML_Syntax.mltyscheme ->
          (FStar_Extraction_ML_Syntax.mlpath * FStar_Ident.lident *
            exp_binding * uenv))
  =
  fun g  ->
    fun ed  ->
      fun nm  ->
        fun ts  ->
          let lid =
            let uu____2754 = FStar_Ident.id_of_text nm  in
            FStar_Syntax_Util.mk_field_projector_name_from_ident
              ed.FStar_Syntax_Syntax.mname uu____2754
             in
          let uu____2755 =
            let uu____2763 =
              FStar_Syntax_Syntax.lid_as_fv lid
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            extend_fv g uu____2763 ts false false  in
          match uu____2755 with
          | (g1,mlid,exp_b) ->
              let mlp =
                let uu____2788 = mlns_of_lid lid  in (uu____2788, mlid)  in
              (mlp, lid, exp_b, g1)
  
let (extend_with_action_name :
  uenv ->
    FStar_Syntax_Syntax.eff_decl ->
      FStar_Syntax_Syntax.action ->
        FStar_Extraction_ML_Syntax.mltyscheme ->
          (FStar_Extraction_ML_Syntax.mlpath * FStar_Ident.lident *
            exp_binding * uenv))
  =
  fun g  ->
    fun ed  ->
      fun a  ->
        fun ts  ->
          let nm =
            ((a.FStar_Syntax_Syntax.action_name).FStar_Ident.ident).FStar_Ident.idText
             in
          let module_name = (ed.FStar_Syntax_Syntax.mname).FStar_Ident.ns  in
          let lid =
            let uu____2831 =
              let uu____2834 =
                let uu____2837 = FStar_Ident.id_of_text nm  in [uu____2837]
                 in
              FStar_List.append module_name uu____2834  in
            FStar_Ident.lid_of_ids uu____2831  in
          let uu____2838 =
            let uu____2846 =
              FStar_Syntax_Syntax.lid_as_fv lid
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            extend_fv g uu____2846 ts false false  in
          match uu____2838 with
          | (g1,mlid,exp_b) ->
              let mlp =
                let uu____2871 = mlns_of_lid lid  in (uu____2871, mlid)  in
              (mlp, lid, exp_b, g1)
  
let (extend_record_field_name :
  uenv ->
    (FStar_Ident.lident * FStar_Ident.ident) ->
      (FStar_Extraction_ML_Syntax.mlpath * uenv))
  =
  fun g  ->
    fun uu____2897  ->
      match uu____2897 with
      | (type_name,fn) ->
          let key =
            FStar_Ident.lid_of_ids
              (FStar_List.append type_name.FStar_Ident.ns [fn])
             in
          let uu____2909 =
            find_uniq g.env_fieldname_map fn.FStar_Ident.idText false  in
          (match uu____2909 with
           | (name,fieldname_map) ->
               let ns = mlns_of_lid key  in
               let mlp = (ns, name)  in
               let g1 =
                 let uu___511_2951 = g  in
                 let uu____2952 =
                   FStar_Util.psmap_add g.mlpath_of_fieldname
                     key.FStar_Ident.str mlp
                    in
                 {
                   env_tcenv = (uu___511_2951.env_tcenv);
                   env_bindings = (uu___511_2951.env_bindings);
                   env_mlident_map = (uu___511_2951.env_mlident_map);
                   mlpath_of_lid = (uu___511_2951.mlpath_of_lid);
                   env_fieldname_map = fieldname_map;
                   mlpath_of_fieldname = uu____2952;
                   tydefs = (uu___511_2951.tydefs);
                   type_names = (uu___511_2951.type_names);
                   currentModule = (uu___511_2951.currentModule)
                 }  in
               (mlp, g1))
  
let (lookup_record_field_name :
  uenv ->
    (FStar_Ident.lident * FStar_Ident.ident) ->
      FStar_Extraction_ML_Syntax.mlpath)
  =
  fun g  ->
    fun uu____2969  ->
      match uu____2969 with
      | (type_name,fn) ->
          let key =
            FStar_Ident.lid_of_ids
              (FStar_List.append type_name.FStar_Ident.ns [fn])
             in
          let uu____2977 =
            FStar_Util.psmap_try_find g.mlpath_of_fieldname
              key.FStar_Ident.str
             in
          (match uu____2977 with
           | FStar_Pervasives_Native.None  ->
               failwith
                 (Prims.op_Hat "Field name not found: " key.FStar_Ident.str)
           | FStar_Pervasives_Native.Some mlp -> mlp)
  
let (extend_with_module_name :
  uenv -> FStar_Ident.lident -> (FStar_Extraction_ML_Syntax.mlpath * uenv)) =
  fun g  ->
    fun m  ->
      let ns = mlns_of_lid m  in
      let p = (m.FStar_Ident.ident).FStar_Ident.idText  in ((ns, p), g)
  
let (exit_module : uenv -> uenv) =
  fun g  ->
    let uu___527_3013 = g  in
    let uu____3014 = initial_mlident_map ()  in
    let uu____3018 = initial_mlident_map ()  in
    {
      env_tcenv = (uu___527_3013.env_tcenv);
      env_bindings = (uu___527_3013.env_bindings);
      env_mlident_map = uu____3014;
      mlpath_of_lid = (uu___527_3013.mlpath_of_lid);
      env_fieldname_map = uu____3018;
      mlpath_of_fieldname = (uu___527_3013.mlpath_of_fieldname);
      tydefs = (uu___527_3013.tydefs);
      type_names = (uu___527_3013.type_names);
      currentModule = (uu___527_3013.currentModule)
    }
  
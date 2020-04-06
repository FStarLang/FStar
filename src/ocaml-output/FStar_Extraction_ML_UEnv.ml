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
  fun projectee  -> match projectee with | Bv _0 -> true | uu____158 -> false 
let (__proj__Bv__item___0 :
  binding -> (FStar_Syntax_Syntax.bv * ty_or_exp_b)) =
  fun projectee  -> match projectee with | Bv _0 -> _0 
let (uu___is_Fv : binding -> Prims.bool) =
  fun projectee  -> match projectee with | Fv _0 -> true | uu____193 -> false 
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
  tydefs: tydef Prims.list ;
  type_names:
    (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_Syntax.mlpath) Prims.list ;
  currentModule: FStar_Extraction_ML_Syntax.mlpath }
let (__proj__Mkuenv__item__env_tcenv : uenv -> FStar_TypeChecker_Env.env) =
  fun projectee  ->
    match projectee with
    | { env_tcenv; env_bindings; env_mlident_map; mlpath_of_lid; tydefs;
        type_names; currentModule;_} -> env_tcenv
  
let (__proj__Mkuenv__item__env_bindings : uenv -> binding Prims.list) =
  fun projectee  ->
    match projectee with
    | { env_tcenv; env_bindings; env_mlident_map; mlpath_of_lid; tydefs;
        type_names; currentModule;_} -> env_bindings
  
let (__proj__Mkuenv__item__env_mlident_map :
  uenv -> FStar_Extraction_ML_Syntax.mlident FStar_Util.psmap) =
  fun projectee  ->
    match projectee with
    | { env_tcenv; env_bindings; env_mlident_map; mlpath_of_lid; tydefs;
        type_names; currentModule;_} -> env_mlident_map
  
let (__proj__Mkuenv__item__mlpath_of_lid :
  uenv -> FStar_Extraction_ML_Syntax.mlpath FStar_Util.psmap) =
  fun projectee  ->
    match projectee with
    | { env_tcenv; env_bindings; env_mlident_map; mlpath_of_lid; tydefs;
        type_names; currentModule;_} -> mlpath_of_lid
  
let (__proj__Mkuenv__item__tydefs : uenv -> tydef Prims.list) =
  fun projectee  ->
    match projectee with
    | { env_tcenv; env_bindings; env_mlident_map; mlpath_of_lid; tydefs;
        type_names; currentModule;_} -> tydefs
  
let (__proj__Mkuenv__item__type_names :
  uenv ->
    (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_Syntax.mlpath) Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { env_tcenv; env_bindings; env_mlident_map; mlpath_of_lid; tydefs;
        type_names; currentModule;_} -> type_names
  
let (__proj__Mkuenv__item__currentModule :
  uenv -> FStar_Extraction_ML_Syntax.mlpath) =
  fun projectee  ->
    match projectee with
    | { env_tcenv; env_bindings; env_mlident_map; mlpath_of_lid; tydefs;
        type_names; currentModule;_} -> currentModule
  
let (tcenv_of_uenv : uenv -> FStar_TypeChecker_Env.env) =
  fun u  -> u.env_tcenv 
let (set_tcenv : uenv -> FStar_TypeChecker_Env.env -> uenv) =
  fun u  ->
    fun t  ->
      let uu___68_665 = u  in
      {
        env_tcenv = t;
        env_bindings = (uu___68_665.env_bindings);
        env_mlident_map = (uu___68_665.env_mlident_map);
        mlpath_of_lid = (uu___68_665.mlpath_of_lid);
        tydefs = (uu___68_665.tydefs);
        type_names = (uu___68_665.type_names);
        currentModule = (uu___68_665.currentModule)
      }
  
let (current_module_of_uenv : uenv -> FStar_Extraction_ML_Syntax.mlpath) =
  fun u  -> u.currentModule 
let (set_current_module : uenv -> FStar_Extraction_ML_Syntax.mlpath -> uenv)
  =
  fun u  ->
    fun m  ->
      let uu___76_683 = u  in
      {
        env_tcenv = (uu___76_683.env_tcenv);
        env_bindings = (uu___76_683.env_bindings);
        env_mlident_map = (uu___76_683.env_mlident_map);
        mlpath_of_lid = (uu___76_683.mlpath_of_lid);
        tydefs = (uu___76_683.tydefs);
        type_names = (uu___76_683.type_names);
        currentModule = m
      }
  
let (bindings_of_uenv : uenv -> binding Prims.list) =
  fun u  -> u.env_bindings 
let (debug : uenv -> (unit -> unit) -> unit) =
  fun g  ->
    fun f  ->
      let c = FStar_Extraction_ML_Syntax.string_of_mlpath g.currentModule  in
      let uu____710 =
        FStar_Options.debug_at_level c (FStar_Options.Other "Extraction")  in
      if uu____710 then f () else ()
  
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
           (uu____741,("FStar"::"Ghost"::[],"erased")) -> true
       | FStar_Extraction_ML_Syntax.MLTY_Named
           (uu____757,("FStar"::"Tactics"::"Effect"::[],"tactic")) ->
           let uu____774 = FStar_Options.codegen ()  in
           uu____774 <> (FStar_Pervasives_Native.Some FStar_Options.Plugin)
       | uu____779 -> false)
  
let (unknownType : FStar_Extraction_ML_Syntax.mlty) =
  FStar_Extraction_ML_Syntax.MLTY_Top 
let (convRange : FStar_Range.range -> Prims.int) = fun r  -> Prims.int_zero 
let (convIdent : FStar_Ident.ident -> FStar_Extraction_ML_Syntax.mlident) =
  fun id1  -> id1.FStar_Ident.idText 
let rec (lookup_ty_local :
  binding Prims.list ->
    FStar_Syntax_Syntax.bv -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun gamma  ->
    fun b  ->
      match gamma with
      | (Bv (b',FStar_Util.Inl ty_b))::tl1 ->
          if FStar_Syntax_Syntax.bv_eq b b'
          then ty_b.ty_b_ty
          else lookup_ty_local tl1 b
      | (Bv (b',FStar_Util.Inr uu____823))::tl1 ->
          if FStar_Syntax_Syntax.bv_eq b b'
          then
            failwith
              (Prims.op_Hat "Type/Expr clash: "
                 (b.FStar_Syntax_Syntax.ppname).FStar_Ident.idText)
          else lookup_ty_local tl1 b
      | uu____831::tl1 -> lookup_ty_local tl1 b
      | [] ->
          failwith
            (Prims.op_Hat "extraction: unbound type var "
               (b.FStar_Syntax_Syntax.ppname).FStar_Ident.idText)
  
let tyscheme_of_td :
  'uuuuuu847 'uuuuuu848 'uuuuuu849 'uuuuuu850 .
    ('uuuuuu847 * 'uuuuuu848 * 'uuuuuu849 *
      FStar_Extraction_ML_Syntax.mlidents * 'uuuuuu850 *
      FStar_Extraction_ML_Syntax.mltybody FStar_Pervasives_Native.option) ->
      FStar_Extraction_ML_Syntax.mltyscheme FStar_Pervasives_Native.option
  =
  fun uu____871  ->
    match uu____871 with
    | (uu____886,uu____887,uu____888,vars,uu____890,body_opt) ->
        (match body_opt with
         | FStar_Pervasives_Native.Some
             (FStar_Extraction_ML_Syntax.MLTD_Abbrev t) ->
             FStar_Pervasives_Native.Some (vars, t)
         | uu____901 -> FStar_Pervasives_Native.None)
  
let (lookup_ty_const :
  uenv ->
    FStar_Extraction_ML_Syntax.mlpath ->
      FStar_Extraction_ML_Syntax.mltyscheme FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun uu____916  ->
      match uu____916 with
      | (module_name,ty_name) ->
          FStar_Util.find_map env.tydefs
            (fun tydef  ->
               if
                 (ty_name = tydef.tydef_name) &&
                   (module_name = tydef.tydef_mlmodule_name)
               then FStar_Pervasives_Native.Some (tydef.tydef_def)
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
        (fun tydef  ->
           if
             (tydef.tydef_name = ty_name) &&
               (tydef.tydef_mlmodule_name = mname)
           then
             match tydef.tydef_mangled_name with
             | FStar_Pervasives_Native.None  ->
                 FStar_Pervasives_Native.Some (mname, ty_name)
             | FStar_Pervasives_Native.Some mangled ->
                 FStar_Pervasives_Native.Some (mname, mangled)
           else FStar_Pervasives_Native.None)
  
let (lookup_tyvar :
  uenv -> FStar_Syntax_Syntax.bv -> FStar_Extraction_ML_Syntax.mlty) =
  fun g  -> fun bt  -> lookup_ty_local g.env_bindings bt 
let (lookup_fv_by_lid : uenv -> FStar_Ident.lident -> ty_or_exp_b) =
  fun g  ->
    fun lid  ->
      let x =
        FStar_Util.find_map g.env_bindings
          (fun uu___0_1081  ->
             match uu___0_1081 with
             | Fv (fv',x) when FStar_Syntax_Syntax.fv_eq_lid fv' lid ->
                 FStar_Pervasives_Native.Some x
             | uu____1086 -> FStar_Pervasives_Native.None)
         in
      match x with
      | FStar_Pervasives_Native.None  ->
          let uu____1087 =
            FStar_Util.format1 "free Variable %s not found\n"
              lid.FStar_Ident.str
             in
          failwith uu____1087
      | FStar_Pervasives_Native.Some y -> FStar_Util.Inr y
  
let (try_lookup_fv :
  uenv ->
    FStar_Syntax_Syntax.fv -> exp_binding FStar_Pervasives_Native.option)
  =
  fun g  ->
    fun fv  ->
      FStar_Util.find_map g.env_bindings
        (fun uu___1_1109  ->
           match uu___1_1109 with
           | Fv (fv',t) when FStar_Syntax_Syntax.fv_eq fv fv' ->
               FStar_Pervasives_Native.Some t
           | uu____1114 -> FStar_Pervasives_Native.None)
  
let (lookup_fv : uenv -> FStar_Syntax_Syntax.fv -> exp_binding) =
  fun g  ->
    fun fv  ->
      let uu____1126 = try_lookup_fv g fv  in
      match uu____1126 with
      | FStar_Pervasives_Native.None  ->
          let uu____1129 =
            let uu____1131 =
              FStar_Range.string_of_range
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.p
               in
            let uu____1133 =
              FStar_Syntax_Print.lid_to_string
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            FStar_Util.format2 "(%s) free Variable %s not found\n" uu____1131
              uu____1133
             in
          failwith uu____1129
      | FStar_Pervasives_Native.Some y -> y
  
let (lookup_bv : uenv -> FStar_Syntax_Syntax.bv -> ty_or_exp_b) =
  fun g  ->
    fun bv  ->
      let x =
        FStar_Util.find_map g.env_bindings
          (fun uu___2_1154  ->
             match uu___2_1154 with
             | Bv (bv',r) when FStar_Syntax_Syntax.bv_eq bv bv' ->
                 FStar_Pervasives_Native.Some r
             | uu____1159 -> FStar_Pervasives_Native.None)
         in
      match x with
      | FStar_Pervasives_Native.None  ->
          let uu____1160 =
            let uu____1162 =
              FStar_Range.string_of_range
                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange
               in
            let uu____1164 = FStar_Syntax_Print.bv_to_string bv  in
            FStar_Util.format2 "(%s) bound Variable %s not found\n"
              uu____1162 uu____1164
             in
          failwith uu____1160
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
          let uu____1200 = lookup_bv g x1  in
          (uu____1200, FStar_Pervasives_Native.None)
      | FStar_Util.Inr x1 ->
          let uu____1204 =
            let uu____1205 = lookup_fv g x1  in FStar_Util.Inr uu____1205  in
          (uu____1204, (x1.FStar_Syntax_Syntax.fv_qual))
  
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
      | uu____1233 -> failwith "Impossible: lookup_term for a non-name"
  
let (sanitize : Prims.string -> Prims.bool -> Prims.string) =
  fun s  ->
    fun is_type1  ->
      let cs = FStar_String.list_of_string s  in
      let sanitize_typ uu____1270 =
        let valid_rest c = FStar_Util.is_letter_or_digit c  in
        let aux cs1 =
          FStar_List.map
            (fun x  ->
               let uu____1301 = valid_rest x  in
               if uu____1301 then x else 117) cs1
           in
        let uu____1308 =
          let uu____1310 = FStar_List.hd cs  in uu____1310 = 39  in
        if uu____1308
        then
          let uu____1319 = FStar_List.hd cs  in
          let uu____1322 =
            let uu____1326 = FStar_List.tail cs  in aux uu____1326  in
          uu____1319 :: uu____1322
        else (let uu____1334 = aux cs  in 39 :: uu____1334)  in
      let sanitize_term uu____1348 =
        let valid c =
          ((FStar_Util.is_letter_or_digit c) || (c = 95)) || (c = 39)  in
        let cs' =
          FStar_List.fold_right
            (fun c  ->
               fun cs1  ->
                 let uu____1379 =
                   let uu____1383 = valid c  in
                   if uu____1383 then [c] else [95; 95]  in
                 FStar_List.append uu____1379 cs1) cs []
           in
        match cs' with
        | c::cs1 when (FStar_Util.is_digit c) || (c = 39) -> 95 :: c :: cs1
        | uu____1415 -> cs  in
      let uu____1419 = if is_type1 then sanitize_typ () else sanitize_term ()
         in
      FStar_String.string_of_list uu____1419
  
let (bv_as_mlident :
  FStar_Syntax_Syntax.bv -> FStar_Extraction_ML_Syntax.mlident) =
  fun x  ->
    let uu____1437 =
      (FStar_Util.starts_with
         (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
         FStar_Ident.reserved_prefix)
        || (FStar_Syntax_Syntax.is_null_bv x)
       in
    if uu____1437
    then
      let uu____1441 =
        let uu____1443 = FStar_Util.string_of_int x.FStar_Syntax_Syntax.index
           in
        Prims.op_Hat "_" uu____1443  in
      Prims.op_Hat (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
        uu____1441
    else (x.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
  
let find_uniq :
  'uuuuuu1457 .
    'uuuuuu1457 FStar_Util.psmap ->
      Prims.string -> Prims.bool -> Prims.string
  =
  fun ml_ident_map  ->
    fun mlident  ->
      fun is_type1  ->
        let mlident1 = sanitize mlident is_type1  in
        let rec aux sm mlident2 i =
          let target_mlident =
            if i = Prims.int_zero
            then mlident2
            else
              (let uu____1517 = FStar_Util.string_of_int i  in
               Prims.op_Hat mlident2 uu____1517)
             in
          let uu____1519 = FStar_Util.psmap_try_find sm target_mlident  in
          match uu____1519 with
          | FStar_Pervasives_Native.Some x ->
              aux sm mlident2 (i + Prims.int_one)
          | FStar_Pervasives_Native.None  -> target_mlident  in
        aux ml_ident_map mlident1 Prims.int_zero
  
let (mlns_of_lid : FStar_Ident.lident -> Prims.string Prims.list) =
  fun x  ->
    FStar_List.map (fun x1  -> x1.FStar_Ident.idText) x.FStar_Ident.ns
  
let (new_mlpath_of_lident :
  uenv -> FStar_Ident.lident -> (FStar_Extraction_ML_Syntax.mlpath * uenv)) =
  fun g  ->
    fun x  ->
      let mlp =
        let uu____1566 =
          FStar_Ident.lid_equals x FStar_Parser_Const.failwith_lid  in
        if uu____1566
        then ([], ((x.FStar_Ident.ident).FStar_Ident.idText))
        else
          (let name =
             find_uniq g.env_mlident_map
               (x.FStar_Ident.ident).FStar_Ident.idText false
              in
           let uu____1588 = mlns_of_lid x  in (uu____1588, name))
         in
      let g1 =
        let uu___273_1597 = g  in
        let uu____1598 =
          FStar_Util.psmap_add g.env_mlident_map
            (FStar_Pervasives_Native.snd mlp) ""
           in
        let uu____1608 =
          FStar_Util.psmap_add g.mlpath_of_lid x.FStar_Ident.str mlp  in
        {
          env_tcenv = (uu___273_1597.env_tcenv);
          env_bindings = (uu___273_1597.env_bindings);
          env_mlident_map = uu____1598;
          mlpath_of_lid = uu____1608;
          tydefs = (uu___273_1597.tydefs);
          type_names = (uu___273_1597.type_names);
          currentModule = (uu___273_1597.currentModule)
        }  in
      (mlp, g1)
  
let (mlpath_of_lident :
  uenv -> FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlpath) =
  fun g  ->
    fun x  ->
      let uu____1622 =
        FStar_Util.psmap_try_find g.mlpath_of_lid x.FStar_Ident.str  in
      match uu____1622 with
      | FStar_Pervasives_Native.None  ->
          failwith (Prims.op_Hat "Identifier not found: " x.FStar_Ident.str)
      | FStar_Pervasives_Native.Some mlp -> mlp
  
let (extend_ty : uenv -> FStar_Syntax_Syntax.bv -> Prims.bool -> uenv) =
  fun g  ->
    fun a  ->
      fun map_to_top  ->
        let is_type1 = Prims.op_Negation map_to_top  in
        let ml_a =
          let uu____1649 = bv_as_mlident a  in
          find_uniq g.env_mlident_map uu____1649 is_type1  in
        let mlident_map = FStar_Util.psmap_add g.env_mlident_map ml_a ""  in
        let mapped_to =
          if map_to_top
          then FStar_Extraction_ML_Syntax.MLTY_Top
          else FStar_Extraction_ML_Syntax.MLTY_Var ml_a  in
        let gamma =
          (Bv (a, (FStar_Util.Inl { ty_b_name = ml_a; ty_b_ty = mapped_to })))
          :: (g.env_bindings)  in
        let tcenv = FStar_TypeChecker_Env.push_bv g.env_tcenv a  in
        let uu___294_1666 = g  in
        {
          env_tcenv = tcenv;
          env_bindings = gamma;
          env_mlident_map = mlident_map;
          mlpath_of_lid = (uu___294_1666.mlpath_of_lid);
          tydefs = (uu___294_1666.tydefs);
          type_names = (uu___294_1666.type_names);
          currentModule = (uu___294_1666.currentModule)
        }
  
let (lookup_ty : uenv -> FStar_Syntax_Syntax.bv -> ty_binding) =
  fun g  ->
    fun x  ->
      let uu____1678 = lookup_bv g x  in
      match uu____1678 with
      | FStar_Util.Inl ty -> ty
      | uu____1680 -> failwith "Expected a type name"
  
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
                | uu____1736 -> FStar_Extraction_ML_Syntax.MLTY_Top  in
              let mlident =
                let uu____1739 = bv_as_mlident x  in
                find_uniq g.env_mlident_map uu____1739 false  in
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
              let exp_binding =
                {
                  exp_b_name = mlident;
                  exp_b_expr = mlx1;
                  exp_b_tscheme = t_x1;
                  exp_b_inst_ok = is_rec
                }  in
              let gamma = (Bv (x, (FStar_Util.Inr exp_binding))) ::
                (g.env_bindings)  in
              let mlident_map =
                FStar_Util.psmap_add g.env_mlident_map mlident ""  in
              let tcenv =
                let uu____1768 = FStar_Syntax_Syntax.binders_of_list [x]  in
                FStar_TypeChecker_Env.push_binders g.env_tcenv uu____1768  in
              ((let uu___328_1771 = g  in
                {
                  env_tcenv = tcenv;
                  env_bindings = gamma;
                  env_mlident_map = mlident_map;
                  mlpath_of_lid = (uu___328_1771.mlpath_of_lid);
                  tydefs = (uu___328_1771.tydefs);
                  type_names = (uu___328_1771.type_names);
                  currentModule = (uu___328_1771.currentModule)
                }), mlident, exp_binding)
  
let (new_mlident : uenv -> (uenv * FStar_Extraction_ML_Syntax.mlident)) =
  fun g  ->
    let ml_ty = FStar_Extraction_ML_Syntax.MLTY_Top  in
    let x =
      FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
        FStar_Syntax_Syntax.tun
       in
    let uu____1790 =
      extend_bv g x ([], FStar_Extraction_ML_Syntax.MLTY_Top) false false
        false
       in
    match uu____1790 with | (g1,id1,uu____1809) -> (g1, id1)
  
let rec (mltyFvars :
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlident Prims.list)
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Var x -> [x]
    | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,f,t2) ->
        let uu____1832 = mltyFvars t1  in
        let uu____1836 = mltyFvars t2  in
        FStar_List.append uu____1832 uu____1836
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
    let uu____1897 = mltyFvars (FStar_Pervasives_Native.snd tys)  in
    subsetMlidents uu____1897 (FStar_Pervasives_Native.fst tys)
  
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
            let uu____1945 = tySchemeIsClosed t_x  in
            if uu____1945
            then
              let ml_ty =
                match t_x with
                | ([],t) -> t
                | uu____1958 -> FStar_Extraction_ML_Syntax.MLTY_Top  in
              let uu____1959 =
                new_mlpath_of_lident g
                  (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                 in
              match uu____1959 with
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
                  let exp_binding =
                    {
                      exp_b_name = mlsymbol;
                      exp_b_expr = mly1;
                      exp_b_tscheme = t_x1;
                      exp_b_inst_ok = is_rec
                    }  in
                  let gamma = (Fv (x, exp_binding)) :: (g1.env_bindings)  in
                  let mlident_map =
                    FStar_Util.psmap_add g1.env_mlident_map mlsymbol ""  in
                  ((let uu___389_2002 = g1  in
                    {
                      env_tcenv = (uu___389_2002.env_tcenv);
                      env_bindings = gamma;
                      env_mlident_map = mlident_map;
                      mlpath_of_lid = (uu___389_2002.mlpath_of_lid);
                      tydefs = (uu___389_2002.tydefs);
                      type_names = (uu___389_2002.type_names);
                      currentModule = (uu___389_2002.currentModule)
                    }), mlsymbol, exp_binding)
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
        let uu____2093 =
          new_mlpath_of_lident g
            (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
           in
        match uu____2093 with
        | (name,g1) ->
            let tydef =
              {
                tydef_fv = fv;
                tydef_mlmodule_name = (FStar_Pervasives_Native.fst name);
                tydef_name = (FStar_Pervasives_Native.snd name);
                tydef_mangled_name = FStar_Pervasives_Native.None;
                tydef_def = ts
              }  in
            (tydef, name,
              (let uu___417_2117 = g1  in
               {
                 env_tcenv = (uu___417_2117.env_tcenv);
                 env_bindings = (uu___417_2117.env_bindings);
                 env_mlident_map = (uu___417_2117.env_mlident_map);
                 mlpath_of_lid = (uu___417_2117.mlpath_of_lid);
                 tydefs = (tydef :: (g1.tydefs));
                 type_names = ((fv, name) :: (g1.type_names));
                 currentModule = (uu___417_2117.currentModule)
               }))
  
let (extend_type_name :
  uenv ->
    FStar_Syntax_Syntax.fv -> (FStar_Extraction_ML_Syntax.mlpath * uenv))
  =
  fun g  ->
    fun fv  ->
      let uu____2141 =
        new_mlpath_of_lident g
          (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
         in
      match uu____2141 with
      | (name,g1) ->
          (name,
            (let uu___426_2153 = g1  in
             {
               env_tcenv = (uu___426_2153.env_tcenv);
               env_bindings = (uu___426_2153.env_bindings);
               env_mlident_map = (uu___426_2153.env_mlident_map);
               mlpath_of_lid = (uu___426_2153.mlpath_of_lid);
               tydefs = (uu___426_2153.tydefs);
               type_names = ((fv, name) :: (g1.type_names));
               currentModule = (uu___426_2153.currentModule)
             }))
  
let (is_type_name : uenv -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun g  ->
    fun fv  ->
      FStar_All.pipe_right g.type_names
        (FStar_Util.for_some
           (fun uu____2184  ->
              match uu____2184 with
              | (x,uu____2191) -> FStar_Syntax_Syntax.fv_eq fv x))
  
let (is_fv_type : uenv -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun g  ->
    fun fv  ->
      (is_type_name g fv) ||
        (FStar_All.pipe_right g.tydefs
           (FStar_Util.for_some
              (fun tydef  -> FStar_Syntax_Syntax.fv_eq fv tydef.tydef_fv)))
  
let (emptyMlPath : FStar_Extraction_ML_Syntax.mlpath) = ([], "") 
let (initial_mlident_map : unit -> Prims.string FStar_Util.psmap) =
  fun uu____2224  ->
    let uu____2225 =
      let uu____2229 =
        let uu____2231 = FStar_Options.codegen ()  in
        uu____2231 = (FStar_Pervasives_Native.Some FStar_Options.FSharp)  in
      if uu____2229
      then FStar_Extraction_ML_Syntax.fsharpkeywords
      else FStar_Extraction_ML_Syntax.ocamlkeywords  in
    let uu____2242 = FStar_Util.psmap_empty ()  in
    FStar_List.fold_right (fun x  -> fun m  -> FStar_Util.psmap_add m x "")
      uu____2225 uu____2242
  
let (mkContext : FStar_TypeChecker_Env.env -> uenv) =
  fun e  ->
    let env =
      let uu____2268 = initial_mlident_map ()  in
      let uu____2272 = FStar_Util.psmap_empty ()  in
      {
        env_tcenv = e;
        env_bindings = [];
        env_mlident_map = uu____2268;
        mlpath_of_lid = uu____2272;
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
    let uu____2299 =
      let uu____2307 =
        let uu____2308 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.failwith_lid
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        FStar_Util.Inr uu____2308  in
      extend_lb env uu____2307 FStar_Syntax_Syntax.tun failwith_ty false
        false
       in
    match uu____2299 with | (g,uu____2312,uu____2313) -> g
  
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
            let uu____2348 = FStar_Ident.id_of_text nm  in
            FStar_Syntax_Util.mk_field_projector_name_from_ident
              ed.FStar_Syntax_Syntax.mname uu____2348
             in
          let uu____2349 =
            let uu____2357 =
              FStar_Syntax_Syntax.lid_as_fv lid
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            extend_fv g uu____2357 ts false false  in
          match uu____2349 with
          | (g1,mlid,exp_b) ->
              let mlp =
                let uu____2382 = mlns_of_lid lid  in (uu____2382, mlid)  in
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
            let uu____2425 =
              let uu____2428 =
                let uu____2431 = FStar_Ident.id_of_text nm  in [uu____2431]
                 in
              FStar_List.append module_name uu____2428  in
            FStar_Ident.lid_of_ids uu____2425  in
          let uu____2432 =
            let uu____2440 =
              FStar_Syntax_Syntax.lid_as_fv lid
                FStar_Syntax_Syntax.delta_constant
                FStar_Pervasives_Native.None
               in
            extend_fv g uu____2440 ts false false  in
          match uu____2432 with
          | (g1,mlid,exp_b) ->
              let mlp =
                let uu____2465 = mlns_of_lid lid  in (uu____2465, mlid)  in
              (mlp, lid, exp_b, g1)
  
let (extend_record_field_name :
  uenv ->
    (FStar_Ident.lident * FStar_Ident.ident) ->
      (FStar_Extraction_ML_Syntax.mlpath * uenv))
  =
  fun g  ->
    fun uu____2491  ->
      match uu____2491 with
      | (ns,fn) ->
          let uu____2502 =
            let uu____2503 =
              let uu____2506 = FStar_Ident.ids_of_lid ns  in
              FStar_List.append uu____2506 [fn]  in
            FStar_Ident.lid_of_ids uu____2503  in
          new_mlpath_of_lident g uu____2502
  
let (lookup_record_field_name :
  uenv ->
    (FStar_Ident.lident * FStar_Ident.ident) ->
      FStar_Extraction_ML_Syntax.mlpath)
  =
  fun g  ->
    fun uu____2523  ->
      match uu____2523 with
      | (ns,fn) ->
          let f =
            let uu____2531 =
              let uu____2534 = FStar_Ident.ids_of_lid ns  in
              FStar_List.append uu____2534 [fn]  in
            FStar_Ident.lid_of_ids uu____2531  in
          mlpath_of_lident g f
  
let (extend_with_module_name :
  uenv -> FStar_Ident.lident -> (FStar_Extraction_ML_Syntax.mlpath * uenv)) =
  fun g  -> fun m  -> new_mlpath_of_lident g m 
let (exit_module : uenv -> uenv) =
  fun g  ->
    let uu___491_2558 = g  in
    let uu____2559 = initial_mlident_map ()  in
    {
      env_tcenv = (uu___491_2558.env_tcenv);
      env_bindings = (uu___491_2558.env_bindings);
      env_mlident_map = uu____2559;
      mlpath_of_lid = (uu___491_2558.mlpath_of_lid);
      tydefs = (uu___491_2558.tydefs);
      type_names = (uu___491_2558.type_names);
      currentModule = (uu___491_2558.currentModule)
    }
  
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
  fun projectee  -> match projectee with | Bv _0 -> true | uu____157 -> false 
let (__proj__Bv__item___0 :
  binding -> (FStar_Syntax_Syntax.bv * ty_or_exp_b)) =
  fun projectee  -> match projectee with | Bv _0 -> _0 
let (uu___is_Fv : binding -> Prims.bool) =
  fun projectee  -> match projectee with | Fv _0 -> true | uu____192 -> false 
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
  
type uenv =
  {
  env_tcenv: FStar_TypeChecker_Env.env ;
  env_bindings: binding Prims.list ;
  env_mlident_map: FStar_Extraction_ML_Syntax.mlident FStar_Util.psmap ;
  tydefs: tydef Prims.list ;
  type_names: FStar_Syntax_Syntax.fv Prims.list ;
  currentModule: FStar_Extraction_ML_Syntax.mlpath }
let (__proj__Mkuenv__item__env_tcenv : uenv -> FStar_TypeChecker_Env.env) =
  fun projectee  ->
    match projectee with
    | { env_tcenv; env_bindings; env_mlident_map; tydefs; type_names;
        currentModule;_} -> env_tcenv
  
let (__proj__Mkuenv__item__env_bindings : uenv -> binding Prims.list) =
  fun projectee  ->
    match projectee with
    | { env_tcenv; env_bindings; env_mlident_map; tydefs; type_names;
        currentModule;_} -> env_bindings
  
let (__proj__Mkuenv__item__env_mlident_map :
  uenv -> FStar_Extraction_ML_Syntax.mlident FStar_Util.psmap) =
  fun projectee  ->
    match projectee with
    | { env_tcenv; env_bindings; env_mlident_map; tydefs; type_names;
        currentModule;_} -> env_mlident_map
  
let (__proj__Mkuenv__item__tydefs : uenv -> tydef Prims.list) =
  fun projectee  ->
    match projectee with
    | { env_tcenv; env_bindings; env_mlident_map; tydefs; type_names;
        currentModule;_} -> tydefs
  
let (__proj__Mkuenv__item__type_names :
  uenv -> FStar_Syntax_Syntax.fv Prims.list) =
  fun projectee  ->
    match projectee with
    | { env_tcenv; env_bindings; env_mlident_map; tydefs; type_names;
        currentModule;_} -> type_names
  
let (__proj__Mkuenv__item__currentModule :
  uenv -> FStar_Extraction_ML_Syntax.mlpath) =
  fun projectee  ->
    match projectee with
    | { env_tcenv; env_bindings; env_mlident_map; tydefs; type_names;
        currentModule;_} -> currentModule
  
let (tcenv_of_uenv : uenv -> FStar_TypeChecker_Env.env) =
  fun u  -> u.env_tcenv 
let (set_tcenv : uenv -> FStar_TypeChecker_Env.env -> uenv) =
  fun u  ->
    fun t  ->
      let uu___62_549 = u  in
      {
        env_tcenv = t;
        env_bindings = (uu___62_549.env_bindings);
        env_mlident_map = (uu___62_549.env_mlident_map);
        tydefs = (uu___62_549.tydefs);
        type_names = (uu___62_549.type_names);
        currentModule = (uu___62_549.currentModule)
      }
  
let (current_module_of_uenv : uenv -> FStar_Extraction_ML_Syntax.mlpath) =
  fun u  -> u.currentModule 
let (set_current_module : uenv -> FStar_Extraction_ML_Syntax.mlpath -> uenv)
  =
  fun u  ->
    fun m  ->
      let uu___70_567 = u  in
      {
        env_tcenv = (uu___70_567.env_tcenv);
        env_bindings = (uu___70_567.env_bindings);
        env_mlident_map = (uu___70_567.env_mlident_map);
        tydefs = (uu___70_567.tydefs);
        type_names = (uu___70_567.type_names);
        currentModule = m
      }
  
let (bindings_of_uenv : uenv -> binding Prims.list) =
  fun u  -> u.env_bindings 
let (debug : uenv -> (unit -> unit) -> unit) =
  fun g  ->
    fun f  ->
      let c = FStar_Extraction_ML_Syntax.string_of_mlpath g.currentModule  in
      let uu____594 =
        FStar_Options.debug_at_level c (FStar_Options.Other "Extraction")  in
      if uu____594 then f () else ()
  
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
           (uu____625,("FStar"::"Ghost"::[],"erased")) -> true
       | FStar_Extraction_ML_Syntax.MLTY_Named
           (uu____641,("FStar"::"Tactics"::"Effect"::[],"tactic")) ->
           let uu____658 = FStar_Options.codegen ()  in
           uu____658 <> (FStar_Pervasives_Native.Some FStar_Options.Plugin)
       | uu____663 -> false)
  
let (unknownType : FStar_Extraction_ML_Syntax.mlty) =
  FStar_Extraction_ML_Syntax.MLTY_Top 
let (prependTick : Prims.string -> Prims.string) =
  fun x  -> if FStar_Util.starts_with x "'" then x else Prims.op_Hat "'A" x 
let (removeTick : Prims.string -> Prims.string) =
  fun x  ->
    if FStar_Util.starts_with x "'"
    then FStar_Util.substring_from x Prims.int_one
    else x
  
let (convRange : FStar_Range.range -> Prims.int) = fun r  -> Prims.int_zero 
let (convIdent : FStar_Ident.ident -> FStar_Extraction_ML_Syntax.mlident) =
  fun id1  -> id1.FStar_Ident.idText 
let (bv_as_ml_tyvar : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun x  ->
    let uu____720 = FStar_Extraction_ML_Syntax.bv_as_mlident x  in
    prependTick uu____720
  
let (bv_as_ml_termvar : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun x  ->
    let uu____729 = FStar_Extraction_ML_Syntax.bv_as_mlident x  in
    removeTick uu____729
  
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
      | (Bv (b',FStar_Util.Inr uu____755))::tl1 ->
          if FStar_Syntax_Syntax.bv_eq b b'
          then
            failwith
              (Prims.op_Hat "Type/Expr clash: "
                 (b.FStar_Syntax_Syntax.ppname).FStar_Ident.idText)
          else lookup_ty_local tl1 b
      | uu____763::tl1 -> lookup_ty_local tl1 b
      | [] ->
          failwith
            (Prims.op_Hat "extraction: unbound type var "
               (b.FStar_Syntax_Syntax.ppname).FStar_Ident.idText)
  
let tyscheme_of_td :
  'Auu____779 'Auu____780 'Auu____781 'Auu____782 .
    ('Auu____779 * 'Auu____780 * 'Auu____781 *
      FStar_Extraction_ML_Syntax.mlidents * 'Auu____782 *
      FStar_Extraction_ML_Syntax.mltybody FStar_Pervasives_Native.option) ->
      FStar_Extraction_ML_Syntax.mltyscheme FStar_Pervasives_Native.option
  =
  fun uu____803  ->
    match uu____803 with
    | (uu____818,uu____819,uu____820,vars,uu____822,body_opt) ->
        (match body_opt with
         | FStar_Pervasives_Native.Some
             (FStar_Extraction_ML_Syntax.MLTD_Abbrev t) ->
             FStar_Pervasives_Native.Some (vars, t)
         | uu____833 -> FStar_Pervasives_Native.None)
  
let (lookup_ty_const :
  uenv ->
    FStar_Extraction_ML_Syntax.mlpath ->
      FStar_Extraction_ML_Syntax.mltyscheme FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun uu____848  ->
      match uu____848 with
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
          (fun uu___0_1013  ->
             match uu___0_1013 with
             | Fv (fv',x) when FStar_Syntax_Syntax.fv_eq_lid fv' lid ->
                 FStar_Pervasives_Native.Some x
             | uu____1018 -> FStar_Pervasives_Native.None)
         in
      match x with
      | FStar_Pervasives_Native.None  ->
          let uu____1019 =
            FStar_Util.format1 "free Variable %s not found\n"
              lid.FStar_Ident.nsstr
             in
          failwith uu____1019
      | FStar_Pervasives_Native.Some y -> FStar_Util.Inr y
  
let (try_lookup_fv :
  uenv ->
    FStar_Syntax_Syntax.fv -> exp_binding FStar_Pervasives_Native.option)
  =
  fun g  ->
    fun fv  ->
      FStar_Util.find_map g.env_bindings
        (fun uu___1_1041  ->
           match uu___1_1041 with
           | Fv (fv',t) when FStar_Syntax_Syntax.fv_eq fv fv' ->
               FStar_Pervasives_Native.Some t
           | uu____1046 -> FStar_Pervasives_Native.None)
  
let (lookup_fv : uenv -> FStar_Syntax_Syntax.fv -> exp_binding) =
  fun g  ->
    fun fv  ->
      let uu____1058 = try_lookup_fv g fv  in
      match uu____1058 with
      | FStar_Pervasives_Native.None  ->
          let uu____1061 =
            let uu____1063 =
              FStar_Range.string_of_range
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.p
               in
            let uu____1065 =
              FStar_Syntax_Print.lid_to_string
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            FStar_Util.format2 "(%s) free Variable %s not found\n" uu____1063
              uu____1065
             in
          failwith uu____1061
      | FStar_Pervasives_Native.Some y -> y
  
let (lookup_bv : uenv -> FStar_Syntax_Syntax.bv -> ty_or_exp_b) =
  fun g  ->
    fun bv  ->
      let x =
        FStar_Util.find_map g.env_bindings
          (fun uu___2_1086  ->
             match uu___2_1086 with
             | Bv (bv',r) when FStar_Syntax_Syntax.bv_eq bv bv' ->
                 FStar_Pervasives_Native.Some r
             | uu____1091 -> FStar_Pervasives_Native.None)
         in
      match x with
      | FStar_Pervasives_Native.None  ->
          let uu____1092 =
            let uu____1094 =
              FStar_Range.string_of_range
                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange
               in
            let uu____1096 = FStar_Syntax_Print.bv_to_string bv  in
            FStar_Util.format2 "(%s) bound Variable %s not found\n"
              uu____1094 uu____1096
             in
          failwith uu____1092
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
          let uu____1132 = lookup_bv g x1  in
          (uu____1132, FStar_Pervasives_Native.None)
      | FStar_Util.Inr x1 ->
          let uu____1136 =
            let uu____1137 = lookup_fv g x1  in FStar_Util.Inr uu____1137  in
          (uu____1136, (x1.FStar_Syntax_Syntax.fv_qual))
  
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
      | uu____1165 -> failwith "Impossible: lookup_term for a non-name"
  
let (extend_ty :
  uenv ->
    FStar_Syntax_Syntax.bv ->
      FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option -> uenv)
  =
  fun g  ->
    fun a  ->
      fun mapped_to  ->
        let ml_a = bv_as_ml_tyvar a  in
        let mapped_to1 =
          match mapped_to with
          | FStar_Pervasives_Native.None  ->
              FStar_Extraction_ML_Syntax.MLTY_Var ml_a
          | FStar_Pervasives_Native.Some t -> t  in
        let gamma =
          (Bv
             (a, (FStar_Util.Inl { ty_b_name = ml_a; ty_b_ty = mapped_to1 })))
          :: (g.env_bindings)  in
        let mlident_map = FStar_Util.psmap_add g.env_mlident_map ml_a ""  in
        let tcenv = FStar_TypeChecker_Env.push_bv g.env_tcenv a  in
        let uu___242_1207 = g  in
        {
          env_tcenv = tcenv;
          env_bindings = gamma;
          env_mlident_map = mlident_map;
          tydefs = (uu___242_1207.tydefs);
          type_names = (uu___242_1207.type_names);
          currentModule = (uu___242_1207.currentModule)
        }
  
let (sanitize : Prims.string -> Prims.string) =
  fun s  ->
    let cs = FStar_String.list_of_string s  in
    let valid c = ((FStar_Util.is_letter_or_digit c) || (c = 95)) || (c = 39)
       in
    let cs' =
      FStar_List.fold_right
        (fun c  ->
           fun cs1  ->
             let uu____1252 =
               let uu____1256 = valid c  in
               if uu____1256 then [c] else [95; 95]  in
             FStar_List.append uu____1252 cs1) cs []
       in
    let cs'1 =
      match cs' with
      | c::cs1 when (FStar_Util.is_digit c) || (c = 39) -> 95 :: c :: cs1
      | uu____1292 -> cs  in
    FStar_String.string_of_list cs'1
  
let find_uniq :
  'Auu____1303 .
    'Auu____1303 FStar_Util.psmap -> Prims.string -> Prims.string
  =
  fun ml_ident_map  ->
    fun mlident  ->
      let mlident1 = sanitize mlident  in
      let rec aux sm mlident2 i =
        let target_mlident =
          if i = Prims.int_zero
          then mlident2
          else
            (let uu____1356 = FStar_Util.string_of_int i  in
             Prims.op_Hat mlident2 uu____1356)
           in
        let uu____1358 = FStar_Util.psmap_try_find sm target_mlident  in
        match uu____1358 with
        | FStar_Pervasives_Native.Some x ->
            aux sm mlident2 (i + Prims.int_one)
        | FStar_Pervasives_Native.None  -> target_mlident  in
      aux ml_ident_map mlident1 Prims.int_zero
  
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
                | uu____1419 -> FStar_Extraction_ML_Syntax.MLTY_Top  in
              let mlident =
                let uu____1422 = FStar_Extraction_ML_Syntax.bv_as_mlident x
                   in
                find_uniq g.env_mlident_map uu____1422  in
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
                let uu____1450 = FStar_Syntax_Syntax.binders_of_list [x]  in
                FStar_TypeChecker_Env.push_binders g.env_tcenv uu____1450  in
              ((let uu___294_1453 = g  in
                {
                  env_tcenv = tcenv;
                  env_bindings = gamma;
                  env_mlident_map = mlident_map;
                  tydefs = (uu___294_1453.tydefs);
                  type_names = (uu___294_1453.type_names);
                  currentModule = (uu___294_1453.currentModule)
                }), mlident, exp_binding)
  
let rec (mltyFvars :
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlident Prims.list)
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Var x -> [x]
    | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,f,t2) ->
        let uu____1473 = mltyFvars t1  in
        let uu____1477 = mltyFvars t2  in
        FStar_List.append uu____1473 uu____1477
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
    let uu____1538 = mltyFvars (FStar_Pervasives_Native.snd tys)  in
    subsetMlidents uu____1538 (FStar_Pervasives_Native.fst tys)
  
let (extend_fv' :
  uenv ->
    FStar_Syntax_Syntax.fv ->
      FStar_Extraction_ML_Syntax.mlpath ->
        FStar_Extraction_ML_Syntax.mltyscheme ->
          Prims.bool ->
            Prims.bool ->
              (uenv * FStar_Extraction_ML_Syntax.mlident * exp_binding))
  =
  fun g  ->
    fun x  ->
      fun y  ->
        fun t_x  ->
          fun add_unit  ->
            fun is_rec  ->
              let uu____1591 = tySchemeIsClosed t_x  in
              if uu____1591
              then
                let ml_ty =
                  match t_x with
                  | ([],t) -> t
                  | uu____1604 -> FStar_Extraction_ML_Syntax.MLTY_Top  in
                let uu____1605 =
                  let uu____1611 = y  in
                  match uu____1611 with
                  | (ns,i) ->
                      let mlsymbol =
                        FStar_Extraction_ML_Syntax.avoid_keyword i  in
                      ((ns, mlsymbol), mlsymbol)
                   in
                match uu____1605 with
                | (mlpath,mlsymbol) ->
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
                    let gamma = (Fv (x, exp_binding)) :: (g.env_bindings)  in
                    let mlident_map =
                      FStar_Util.psmap_add g.env_mlident_map mlsymbol ""  in
                    ((let uu___352_1668 = g  in
                      {
                        env_tcenv = (uu___352_1668.env_tcenv);
                        env_bindings = gamma;
                        env_mlident_map = mlident_map;
                        tydefs = (uu___352_1668.tydefs);
                        type_names = (uu___352_1668.type_names);
                        currentModule = (uu___352_1668.currentModule)
                      }), mlsymbol, exp_binding)
              else failwith "freevars found"
  
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
            let mlp =
              FStar_Extraction_ML_Syntax.mlpath_of_lident
                (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            extend_fv' g x mlp t_x add_unit is_rec
  
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
              | FStar_Util.Inr f ->
                  let uu____1776 =
                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                      (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                     in
                  (match uu____1776 with
                   | (p,y) -> extend_fv' g f (p, y) t_x add_unit is_rec)
  
let (extend_tydef :
  uenv ->
    FStar_Syntax_Syntax.fv ->
      FStar_Extraction_ML_Syntax.one_mltydecl -> (uenv * tydef))
  =
  fun g  ->
    fun fv  ->
      fun td  ->
        let m = module_name_of_fv fv  in
        let uu____1826 = td  in
        match uu____1826 with
        | (_assumed,name,mangled,vars,metadata,body_opt) ->
            let tydef =
              let uu____1852 =
                let uu____1853 = tyscheme_of_td td  in
                FStar_Option.get uu____1853  in
              {
                tydef_fv = fv;
                tydef_mlmodule_name = m;
                tydef_name = name;
                tydef_mangled_name = mangled;
                tydef_def = uu____1852
              }  in
            ((let uu___399_1862 = g  in
              {
                env_tcenv = (uu___399_1862.env_tcenv);
                env_bindings = (uu___399_1862.env_bindings);
                env_mlident_map = (uu___399_1862.env_mlident_map);
                tydefs = (tydef :: (g.tydefs));
                type_names = (fv :: (g.type_names));
                currentModule = (uu___399_1862.currentModule)
              }), tydef)
  
let (extend_type_name : uenv -> FStar_Syntax_Syntax.fv -> uenv) =
  fun g  ->
    fun fv  ->
      let uu___405_1874 = g  in
      {
        env_tcenv = (uu___405_1874.env_tcenv);
        env_bindings = (uu___405_1874.env_bindings);
        env_mlident_map = (uu___405_1874.env_mlident_map);
        tydefs = (uu___405_1874.tydefs);
        type_names = (fv :: (g.type_names));
        currentModule = (uu___405_1874.currentModule)
      }
  
let (is_type_name : uenv -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun g  ->
    fun fv  ->
      FStar_All.pipe_right g.type_names
        (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq fv))
  
let (is_fv_type : uenv -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun g  ->
    fun fv  ->
      (is_type_name g fv) ||
        (FStar_All.pipe_right g.tydefs
           (FStar_Util.for_some
              (fun tydef  -> FStar_Syntax_Syntax.fv_eq fv tydef.tydef_fv)))
  
let (emptyMlPath : FStar_Extraction_ML_Syntax.mlpath) = ([], "") 
let (mkContext : FStar_TypeChecker_Env.env -> uenv) =
  fun e  ->
    let env =
      let uu____1921 = FStar_Util.psmap_empty ()  in
      {
        env_tcenv = e;
        env_bindings = [];
        env_mlident_map = uu____1921;
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
    let uu____1946 =
      let uu____1954 =
        let uu____1955 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.failwith_lid
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        FStar_Util.Inr uu____1955  in
      extend_lb env uu____1954 FStar_Syntax_Syntax.tun failwith_ty false
        false
       in
    match uu____1946 with | (g,uu____1959,uu____1960) -> g
  
let (monad_op_name :
  FStar_Syntax_Syntax.eff_decl ->
    Prims.string -> (FStar_Extraction_ML_Syntax.mlpath * FStar_Ident.lident))
  =
  fun ed  ->
    fun nm  ->
      let lid =
        let uu____1981 = FStar_Ident.id_of_text nm  in
        FStar_Syntax_Util.mk_field_projector_name_from_ident
          ed.FStar_Syntax_Syntax.mname uu____1981
         in
      let uu____1982 = FStar_Extraction_ML_Syntax.mlpath_of_lident lid  in
      (uu____1982, lid)
  
let (action_name :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.action ->
      (FStar_Extraction_ML_Syntax.mlpath * FStar_Ident.lident))
  =
  fun ed  ->
    fun a  ->
      let nm =
        ((a.FStar_Syntax_Syntax.action_name).FStar_Ident.ident).FStar_Ident.idText
         in
      let module_name = (ed.FStar_Syntax_Syntax.mname).FStar_Ident.ns  in
      let lid =
        let uu____2004 =
          let uu____2007 =
            let uu____2010 = FStar_Ident.id_of_text nm  in [uu____2010]  in
          FStar_List.append module_name uu____2007  in
        FStar_Ident.lid_of_ids uu____2004  in
      let uu____2011 = FStar_Extraction_ML_Syntax.mlpath_of_lident lid  in
      (uu____2011, lid)
  
let (extend_with_iface :
  uenv ->
    FStar_Extraction_ML_Syntax.mlpath ->
      (FStar_Syntax_Syntax.fv * exp_binding) Prims.list ->
        tydef Prims.list -> FStar_Syntax_Syntax.fv Prims.list -> uenv)
  =
  fun g  ->
    fun m  ->
      fun bs  ->
        fun tds  ->
          fun tns  ->
            let mlident_map =
              FStar_List.fold_left
                (fun acc  ->
                   fun uu____2074  ->
                     match uu____2074 with
                     | (uu____2085,x) ->
                         FStar_Util.psmap_add acc x.exp_b_name "")
                g.env_mlident_map bs
               in
            let uu___449_2089 = g  in
            let uu____2090 =
              let uu____2093 = FStar_List.map (fun _2100  -> Fv _2100) bs  in
              FStar_List.append uu____2093 g.env_bindings  in
            {
              env_tcenv = (uu___449_2089.env_tcenv);
              env_bindings = uu____2090;
              env_mlident_map = mlident_map;
              tydefs = (FStar_List.append tds g.tydefs);
              type_names = (FStar_List.append tns g.type_names);
              currentModule = (uu___449_2089.currentModule)
            }
  
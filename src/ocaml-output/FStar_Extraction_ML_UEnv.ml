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
      | (Bv (b',FStar_Util.Inr uu____707))::tl1 ->
          if FStar_Syntax_Syntax.bv_eq b b'
          then
            failwith
              (Prims.op_Hat "Type/Expr clash: "
                 (b.FStar_Syntax_Syntax.ppname).FStar_Ident.idText)
          else lookup_ty_local tl1 b
      | uu____715::tl1 -> lookup_ty_local tl1 b
      | [] ->
          failwith
            (Prims.op_Hat "extraction: unbound type var "
               (b.FStar_Syntax_Syntax.ppname).FStar_Ident.idText)
  
let tyscheme_of_td :
  'uu____731 'uu____732 'uu____733 'uu____734 .
    ('uu____731 * 'uu____732 * 'uu____733 *
      FStar_Extraction_ML_Syntax.mlidents * 'uu____734 *
      FStar_Extraction_ML_Syntax.mltybody FStar_Pervasives_Native.option) ->
      FStar_Extraction_ML_Syntax.mltyscheme FStar_Pervasives_Native.option
  =
  fun uu____755  ->
    match uu____755 with
    | (uu____770,uu____771,uu____772,vars,uu____774,body_opt) ->
        (match body_opt with
         | FStar_Pervasives_Native.Some
             (FStar_Extraction_ML_Syntax.MLTD_Abbrev t) ->
             FStar_Pervasives_Native.Some (vars, t)
         | uu____785 -> FStar_Pervasives_Native.None)
  
let (lookup_ty_const :
  uenv ->
    FStar_Extraction_ML_Syntax.mlpath ->
      FStar_Extraction_ML_Syntax.mltyscheme FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun uu____800  ->
      match uu____800 with
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
          (fun uu___0_965  ->
             match uu___0_965 with
             | Fv (fv',x) when FStar_Syntax_Syntax.fv_eq_lid fv' lid ->
                 FStar_Pervasives_Native.Some x
             | uu____970 -> FStar_Pervasives_Native.None)
         in
      match x with
      | FStar_Pervasives_Native.None  ->
          let uu____971 =
            FStar_Util.format1 "free Variable %s not found\n"
              lid.FStar_Ident.nsstr
             in
          failwith uu____971
      | FStar_Pervasives_Native.Some y -> FStar_Util.Inr y
  
let (try_lookup_fv :
  uenv ->
    FStar_Syntax_Syntax.fv -> exp_binding FStar_Pervasives_Native.option)
  =
  fun g  ->
    fun fv  ->
      FStar_Util.find_map g.env_bindings
        (fun uu___1_993  ->
           match uu___1_993 with
           | Fv (fv',t) when FStar_Syntax_Syntax.fv_eq fv fv' ->
               FStar_Pervasives_Native.Some t
           | uu____998 -> FStar_Pervasives_Native.None)
  
let (lookup_fv : uenv -> FStar_Syntax_Syntax.fv -> exp_binding) =
  fun g  ->
    fun fv  ->
      let uu____1010 = try_lookup_fv g fv  in
      match uu____1010 with
      | FStar_Pervasives_Native.None  ->
          let uu____1013 =
            let uu____1015 =
              FStar_Range.string_of_range
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.p
               in
            let uu____1017 =
              FStar_Syntax_Print.lid_to_string
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            FStar_Util.format2 "(%s) free Variable %s not found\n" uu____1015
              uu____1017
             in
          failwith uu____1013
      | FStar_Pervasives_Native.Some y -> y
  
let (lookup_bv : uenv -> FStar_Syntax_Syntax.bv -> ty_or_exp_b) =
  fun g  ->
    fun bv  ->
      let x =
        FStar_Util.find_map g.env_bindings
          (fun uu___2_1038  ->
             match uu___2_1038 with
             | Bv (bv',r) when FStar_Syntax_Syntax.bv_eq bv bv' ->
                 FStar_Pervasives_Native.Some r
             | uu____1043 -> FStar_Pervasives_Native.None)
         in
      match x with
      | FStar_Pervasives_Native.None  ->
          let uu____1044 =
            let uu____1046 =
              FStar_Range.string_of_range
                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange
               in
            let uu____1048 = FStar_Syntax_Print.bv_to_string bv  in
            FStar_Util.format2 "(%s) bound Variable %s not found\n"
              uu____1046 uu____1048
             in
          failwith uu____1044
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
          let uu____1084 = lookup_bv g x1  in
          (uu____1084, FStar_Pervasives_Native.None)
      | FStar_Util.Inr x1 ->
          let uu____1088 =
            let uu____1089 = lookup_fv g x1  in FStar_Util.Inr uu____1089  in
          (uu____1088, (x1.FStar_Syntax_Syntax.fv_qual))
  
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
      | uu____1117 -> failwith "Impossible: lookup_term for a non-name"
  
let (sanitize : Prims.string -> Prims.bool -> Prims.string) =
  fun s  ->
    fun is_type1  ->
      let cs = FStar_String.list_of_string s  in
      let valid c =
        ((FStar_Util.is_letter_or_digit c) || (c = 95)) || (c = 39)  in
      let cs' =
        FStar_List.fold_right
          (fun c  ->
             fun cs1  ->
               let uu____1176 =
                 let uu____1180 = valid c  in
                 if uu____1180 then [c] else [95; 95]  in
               FStar_List.append uu____1176 cs1) cs []
         in
      let cs'1 =
        match cs' with
        | c::cs1 when
            (FStar_Util.is_digit c) ||
              ((Prims.op_Negation is_type1) && (c = 39))
            -> 95 :: c :: cs1
        | uu____1216 -> cs  in
      FStar_String.string_of_list cs'1
  
let find_uniq :
  'uu____1229 .
    'uu____1229 FStar_Util.psmap ->
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
              (let uu____1289 = FStar_Util.string_of_int i  in
               Prims.op_Hat mlident2 uu____1289)
             in
          let uu____1291 = FStar_Util.psmap_try_find sm target_mlident  in
          match uu____1291 with
          | FStar_Pervasives_Native.Some x ->
              aux sm mlident2 (i + Prims.int_one)
          | FStar_Pervasives_Native.None  -> target_mlident  in
        aux ml_ident_map mlident1 Prims.int_zero
  
let (extend_ty : uenv -> FStar_Syntax_Syntax.bv -> Prims.bool -> uenv) =
  fun g  ->
    fun a  ->
      fun map_to_top  ->
        let is_type1 = Prims.op_Negation map_to_top  in
        let ml_a = FStar_Extraction_ML_Syntax.bv_as_mlident a  in
        let ml_a1 =
          if map_to_top
          then ml_a
          else
            (let ml_a1 =
               if FStar_Util.starts_with ml_a "'"
               then ml_a
               else Prims.op_Hat "'" ml_a  in
             if FStar_Util.starts_with ml_a1 "'_"
             then
               let uu____1337 =
                 FStar_Util.substring_from ml_a1 (Prims.of_int (2))  in
               Prims.op_Hat "'A" uu____1337
             else ml_a1)
           in
        let ml_a2 = find_uniq g.env_mlident_map ml_a1 is_type1  in
        let mlident_map = FStar_Util.psmap_add g.env_mlident_map ml_a2 ""  in
        let mapped_to =
          if map_to_top
          then FStar_Extraction_ML_Syntax.MLTY_Top
          else FStar_Extraction_ML_Syntax.MLTY_Var ml_a2  in
        let gamma =
          (Bv
             (a, (FStar_Util.Inl { ty_b_name = ml_a2; ty_b_ty = mapped_to })))
          :: (g.env_bindings)  in
        let tcenv = FStar_TypeChecker_Env.push_bv g.env_tcenv a  in
        let uu___266_1360 = g  in
        {
          env_tcenv = tcenv;
          env_bindings = gamma;
          env_mlident_map = mlident_map;
          tydefs = (uu___266_1360.tydefs);
          type_names = (uu___266_1360.type_names);
          currentModule = (uu___266_1360.currentModule)
        }
  
let (lookup_ty : uenv -> FStar_Syntax_Syntax.bv -> ty_binding) =
  fun g  ->
    fun x  ->
      let uu____1372 = lookup_bv g x  in
      match uu____1372 with
      | FStar_Util.Inl ty -> ty
      | uu____1374 -> failwith "Expected a type name"
  
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
                | uu____1430 -> FStar_Extraction_ML_Syntax.MLTY_Top  in
              let mlident =
                let uu____1433 = FStar_Extraction_ML_Syntax.bv_as_mlident x
                   in
                find_uniq g.env_mlident_map uu____1433 false  in
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
                let uu____1462 = FStar_Syntax_Syntax.binders_of_list [x]  in
                FStar_TypeChecker_Env.push_binders g.env_tcenv uu____1462  in
              ((let uu___300_1465 = g  in
                {
                  env_tcenv = tcenv;
                  env_bindings = gamma;
                  env_mlident_map = mlident_map;
                  tydefs = (uu___300_1465.tydefs);
                  type_names = (uu___300_1465.type_names);
                  currentModule = (uu___300_1465.currentModule)
                }), mlident, exp_binding)
  
let (new_mlident : uenv -> (uenv * FStar_Extraction_ML_Syntax.mlident)) =
  fun g  ->
    let ml_ty = FStar_Extraction_ML_Syntax.MLTY_Top  in
    let x =
      FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
        FStar_Syntax_Syntax.tun
       in
    let uu____1484 =
      extend_bv g x ([], FStar_Extraction_ML_Syntax.MLTY_Top) false false
        false
       in
    match uu____1484 with | (g1,id1,uu____1503) -> (g1, id1)
  
let rec (mltyFvars :
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlident Prims.list)
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Var x -> [x]
    | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,f,t2) ->
        let uu____1526 = mltyFvars t1  in
        let uu____1530 = mltyFvars t2  in
        FStar_List.append uu____1526 uu____1530
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
    let uu____1591 = mltyFvars (FStar_Pervasives_Native.snd tys)  in
    subsetMlidents uu____1591 (FStar_Pervasives_Native.fst tys)
  
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
              let uu____1644 = tySchemeIsClosed t_x  in
              if uu____1644
              then
                let ml_ty =
                  match t_x with
                  | ([],t) -> t
                  | uu____1657 -> FStar_Extraction_ML_Syntax.MLTY_Top  in
                let uu____1658 =
                  let uu____1664 = y  in
                  match uu____1664 with
                  | (ns,i) ->
                      let mlsymbol =
                        FStar_Extraction_ML_Syntax.avoid_keyword i  in
                      ((ns, mlsymbol), mlsymbol)
                   in
                match uu____1658 with
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
                    ((let uu___366_1721 = g  in
                      {
                        env_tcenv = (uu___366_1721.env_tcenv);
                        env_bindings = gamma;
                        env_mlident_map = mlident_map;
                        tydefs = (uu___366_1721.tydefs);
                        type_names = (uu___366_1721.type_names);
                        currentModule = (uu___366_1721.currentModule)
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
                  let uu____1829 =
                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                      (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                     in
                  (match uu____1829 with
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
        let uu____1879 = td  in
        match uu____1879 with
        | (_assumed,name,mangled,vars,metadata,body_opt) ->
            let tydef =
              let uu____1905 =
                let uu____1906 = tyscheme_of_td td  in
                FStar_Option.get uu____1906  in
              {
                tydef_fv = fv;
                tydef_mlmodule_name = m;
                tydef_name = name;
                tydef_mangled_name = mangled;
                tydef_def = uu____1905
              }  in
            ((let uu___413_1915 = g  in
              {
                env_tcenv = (uu___413_1915.env_tcenv);
                env_bindings = (uu___413_1915.env_bindings);
                env_mlident_map = (uu___413_1915.env_mlident_map);
                tydefs = (tydef :: (g.tydefs));
                type_names = (fv :: (g.type_names));
                currentModule = (uu___413_1915.currentModule)
              }), tydef)
  
let (extend_type_name : uenv -> FStar_Syntax_Syntax.fv -> uenv) =
  fun g  ->
    fun fv  ->
      let uu___419_1927 = g  in
      {
        env_tcenv = (uu___419_1927.env_tcenv);
        env_bindings = (uu___419_1927.env_bindings);
        env_mlident_map = (uu___419_1927.env_mlident_map);
        tydefs = (uu___419_1927.tydefs);
        type_names = (fv :: (g.type_names));
        currentModule = (uu___419_1927.currentModule)
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
      let uu____1974 = FStar_Util.psmap_empty ()  in
      {
        env_tcenv = e;
        env_bindings = [];
        env_mlident_map = uu____1974;
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
    let uu____1999 =
      let uu____2007 =
        let uu____2008 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.failwith_lid
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        FStar_Util.Inr uu____2008  in
      extend_lb env uu____2007 FStar_Syntax_Syntax.tun failwith_ty false
        false
       in
    match uu____1999 with | (g,uu____2012,uu____2013) -> g
  
let (monad_op_name :
  FStar_Syntax_Syntax.eff_decl ->
    Prims.string -> (FStar_Extraction_ML_Syntax.mlpath * FStar_Ident.lident))
  =
  fun ed  ->
    fun nm  ->
      let lid =
        let uu____2034 = FStar_Ident.id_of_text nm  in
        FStar_Syntax_Util.mk_field_projector_name_from_ident
          ed.FStar_Syntax_Syntax.mname uu____2034
         in
      let uu____2035 = FStar_Extraction_ML_Syntax.mlpath_of_lident lid  in
      (uu____2035, lid)
  
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
        let uu____2057 =
          let uu____2060 =
            let uu____2063 = FStar_Ident.id_of_text nm  in [uu____2063]  in
          FStar_List.append module_name uu____2060  in
        FStar_Ident.lid_of_ids uu____2057  in
      let uu____2064 = FStar_Extraction_ML_Syntax.mlpath_of_lident lid  in
      (uu____2064, lid)
  
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
                   fun uu____2127  ->
                     match uu____2127 with
                     | (uu____2138,x) ->
                         FStar_Util.psmap_add acc x.exp_b_name "")
                g.env_mlident_map bs
               in
            let uu___463_2142 = g  in
            let uu____2143 =
              let uu____2146 =
                FStar_List.map (fun uu____2153  -> Fv uu____2153) bs  in
              FStar_List.append uu____2146 g.env_bindings  in
            {
              env_tcenv = (uu___463_2142.env_tcenv);
              env_bindings = uu____2143;
              env_mlident_map = mlident_map;
              tydefs = (FStar_List.append tds g.tydefs);
              type_names = (FStar_List.append tns g.type_names);
              currentModule = (uu___463_2142.currentModule)
            }
  
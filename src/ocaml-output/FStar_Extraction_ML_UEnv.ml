open Prims
type ty_binding =
  {
  ty_b_name: FStar_Extraction_ML_Syntax.mlident ;
  ty_b_ty: FStar_Extraction_ML_Syntax.mlty }
let (__proj__Mkty_binding__item__ty_b_name :
  ty_binding -> FStar_Extraction_ML_Syntax.mlident) =
  fun projectee ->
    match projectee with | { ty_b_name; ty_b_ty;_} -> ty_b_name
let (__proj__Mkty_binding__item__ty_b_ty :
  ty_binding -> FStar_Extraction_ML_Syntax.mlty) =
  fun projectee -> match projectee with | { ty_b_name; ty_b_ty;_} -> ty_b_ty
type exp_binding =
  {
  exp_b_name: FStar_Extraction_ML_Syntax.mlident ;
  exp_b_expr: FStar_Extraction_ML_Syntax.mlexpr ;
  exp_b_tscheme: FStar_Extraction_ML_Syntax.mltyscheme ;
  exp_b_inst_ok: Prims.bool }
let (__proj__Mkexp_binding__item__exp_b_name :
  exp_binding -> FStar_Extraction_ML_Syntax.mlident) =
  fun projectee ->
    match projectee with
    | { exp_b_name; exp_b_expr; exp_b_tscheme; exp_b_inst_ok;_} -> exp_b_name
let (__proj__Mkexp_binding__item__exp_b_expr :
  exp_binding -> FStar_Extraction_ML_Syntax.mlexpr) =
  fun projectee ->
    match projectee with
    | { exp_b_name; exp_b_expr; exp_b_tscheme; exp_b_inst_ok;_} -> exp_b_expr
let (__proj__Mkexp_binding__item__exp_b_tscheme :
  exp_binding -> FStar_Extraction_ML_Syntax.mltyscheme) =
  fun projectee ->
    match projectee with
    | { exp_b_name; exp_b_expr; exp_b_tscheme; exp_b_inst_ok;_} ->
        exp_b_tscheme
let (__proj__Mkexp_binding__item__exp_b_inst_ok : exp_binding -> Prims.bool)
  =
  fun projectee ->
    match projectee with
    | { exp_b_name; exp_b_expr; exp_b_tscheme; exp_b_inst_ok;_} ->
        exp_b_inst_ok
type ty_or_exp_b = (ty_binding, exp_binding) FStar_Util.either
type binding =
  | Bv of (FStar_Syntax_Syntax.bv * ty_or_exp_b) 
  | Fv of (FStar_Syntax_Syntax.fv * exp_binding) 
let (uu___is_Bv : binding -> Prims.bool) =
  fun projectee -> match projectee with | Bv _0 -> true | uu____156 -> false
let (__proj__Bv__item___0 :
  binding -> (FStar_Syntax_Syntax.bv * ty_or_exp_b)) =
  fun projectee -> match projectee with | Bv _0 -> _0
let (uu___is_Fv : binding -> Prims.bool) =
  fun projectee -> match projectee with | Fv _0 -> true | uu____191 -> false
let (__proj__Fv__item___0 :
  binding -> (FStar_Syntax_Syntax.fv * exp_binding)) =
  fun projectee -> match projectee with | Fv _0 -> _0
type tydef =
  {
  tydef_fv: FStar_Syntax_Syntax.fv ;
  tydef_mlmodule_name: FStar_Extraction_ML_Syntax.mlsymbol Prims.list ;
  tydef_name: FStar_Extraction_ML_Syntax.mlsymbol ;
  tydef_mangled_name:
    FStar_Extraction_ML_Syntax.mlsymbol FStar_Pervasives_Native.option ;
  tydef_def: FStar_Extraction_ML_Syntax.mltyscheme }
let (__proj__Mktydef__item__tydef_fv : tydef -> FStar_Syntax_Syntax.fv) =
  fun projectee ->
    match projectee with
    | { tydef_fv; tydef_mlmodule_name; tydef_name; tydef_mangled_name;
        tydef_def;_} -> tydef_fv
let (__proj__Mktydef__item__tydef_mlmodule_name :
  tydef -> FStar_Extraction_ML_Syntax.mlsymbol Prims.list) =
  fun projectee ->
    match projectee with
    | { tydef_fv; tydef_mlmodule_name; tydef_name; tydef_mangled_name;
        tydef_def;_} -> tydef_mlmodule_name
let (__proj__Mktydef__item__tydef_name :
  tydef -> FStar_Extraction_ML_Syntax.mlsymbol) =
  fun projectee ->
    match projectee with
    | { tydef_fv; tydef_mlmodule_name; tydef_name; tydef_mangled_name;
        tydef_def;_} -> tydef_name
let (__proj__Mktydef__item__tydef_mangled_name :
  tydef -> FStar_Extraction_ML_Syntax.mlsymbol FStar_Pervasives_Native.option)
  =
  fun projectee ->
    match projectee with
    | { tydef_fv; tydef_mlmodule_name; tydef_name; tydef_mangled_name;
        tydef_def;_} -> tydef_mangled_name
let (__proj__Mktydef__item__tydef_def :
  tydef -> FStar_Extraction_ML_Syntax.mltyscheme) =
  fun projectee ->
    match projectee with
    | { tydef_fv; tydef_mlmodule_name; tydef_name; tydef_mangled_name;
        tydef_def;_} -> tydef_def
type uenv =
  {
  env_tcenv: FStar_TypeChecker_Env.env ;
  env_bindings: binding Prims.list ;
  tydefs: tydef Prims.list ;
  type_names: FStar_Syntax_Syntax.fv Prims.list ;
  currentModule: FStar_Extraction_ML_Syntax.mlpath }
let (__proj__Mkuenv__item__env_tcenv : uenv -> FStar_TypeChecker_Env.env) =
  fun projectee ->
    match projectee with
    | { env_tcenv; env_bindings; tydefs; type_names; currentModule;_} ->
        env_tcenv
let (__proj__Mkuenv__item__env_bindings : uenv -> binding Prims.list) =
  fun projectee ->
    match projectee with
    | { env_tcenv; env_bindings; tydefs; type_names; currentModule;_} ->
        env_bindings
let (__proj__Mkuenv__item__tydefs : uenv -> tydef Prims.list) =
  fun projectee ->
    match projectee with
    | { env_tcenv; env_bindings; tydefs; type_names; currentModule;_} ->
        tydefs
let (__proj__Mkuenv__item__type_names :
  uenv -> FStar_Syntax_Syntax.fv Prims.list) =
  fun projectee ->
    match projectee with
    | { env_tcenv; env_bindings; tydefs; type_names; currentModule;_} ->
        type_names
let (__proj__Mkuenv__item__currentModule :
  uenv -> FStar_Extraction_ML_Syntax.mlpath) =
  fun projectee ->
    match projectee with
    | { env_tcenv; env_bindings; tydefs; type_names; currentModule;_} ->
        currentModule
let (debug : uenv -> (unit -> unit) -> unit) =
  fun g ->
    fun f ->
      let c = FStar_Extraction_ML_Syntax.string_of_mlpath g.currentModule in
      let uu____494 =
        FStar_Options.debug_at_level c (FStar_Options.Other "Extraction") in
      if uu____494 then f () else ()
let (mkFvvar :
  FStar_Ident.lident -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.fv) =
  fun l ->
    fun t ->
      FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.delta_constant
        FStar_Pervasives_Native.None
let (erasedContent : FStar_Extraction_ML_Syntax.mlty) =
  FStar_Extraction_ML_Syntax.MLTY_Erased
let (erasableTypeNoDelta : FStar_Extraction_ML_Syntax.mlty -> Prims.bool) =
  fun t ->
    if t = FStar_Extraction_ML_Syntax.ml_unit_ty
    then true
    else
      (match t with
       | FStar_Extraction_ML_Syntax.MLTY_Named
           (uu____525, ("FStar"::"Ghost"::[], "erased")) -> true
       | FStar_Extraction_ML_Syntax.MLTY_Named
           (uu____541, ("FStar"::"Tactics"::"Effect"::[], "tactic")) ->
           let uu____558 = FStar_Options.codegen () in
           uu____558 <> (FStar_Pervasives_Native.Some FStar_Options.Plugin)
       | uu____563 -> false)
let (unknownType : FStar_Extraction_ML_Syntax.mlty) =
  FStar_Extraction_ML_Syntax.MLTY_Top
let (prependTick : Prims.string -> Prims.string) =
  fun x -> if FStar_Util.starts_with x "'" then x else Prims.op_Hat "'A" x
let (removeTick : Prims.string -> Prims.string) =
  fun x ->
    if FStar_Util.starts_with x "'"
    then FStar_Util.substring_from x (Prims.parse_int "1")
    else x
let (convRange : FStar_Range.range -> Prims.int) =
  fun r -> (Prims.parse_int "0")
let (convIdent : FStar_Ident.ident -> FStar_Extraction_ML_Syntax.mlident) =
  fun id1 -> id1.FStar_Ident.idText
let (bv_as_ml_tyvar : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun x ->
    let uu____620 = FStar_Extraction_ML_Syntax.bv_as_mlident x in
    prependTick uu____620
let (bv_as_ml_termvar : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun x ->
    let uu____629 = FStar_Extraction_ML_Syntax.bv_as_mlident x in
    removeTick uu____629
let rec (lookup_ty_local :
  binding Prims.list ->
    FStar_Syntax_Syntax.bv -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun gamma ->
    fun b ->
      match gamma with
      | (Bv (b', FStar_Util.Inl ty_b))::tl1 ->
          if FStar_Syntax_Syntax.bv_eq b b'
          then ty_b.ty_b_ty
          else lookup_ty_local tl1 b
      | (Bv (b', FStar_Util.Inr uu____655))::tl1 ->
          if FStar_Syntax_Syntax.bv_eq b b'
          then
            failwith
              (Prims.op_Hat "Type/Expr clash: "
                 (b.FStar_Syntax_Syntax.ppname).FStar_Ident.idText)
          else lookup_ty_local tl1 b
      | uu____663::tl1 -> lookup_ty_local tl1 b
      | [] ->
          failwith
            (Prims.op_Hat "extraction: unbound type var "
               (b.FStar_Syntax_Syntax.ppname).FStar_Ident.idText)
let tyscheme_of_td :
  'Auu____679 'Auu____680 'Auu____681 'Auu____682 .
    ('Auu____679 * 'Auu____680 * 'Auu____681 *
      FStar_Extraction_ML_Syntax.mlidents * 'Auu____682 *
      FStar_Extraction_ML_Syntax.mltybody FStar_Pervasives_Native.option) ->
      FStar_Extraction_ML_Syntax.mltyscheme FStar_Pervasives_Native.option
  =
  fun uu____703 ->
    match uu____703 with
    | (uu____718, uu____719, uu____720, vars, uu____722, body_opt) ->
        (match body_opt with
         | FStar_Pervasives_Native.Some
             (FStar_Extraction_ML_Syntax.MLTD_Abbrev t) ->
             FStar_Pervasives_Native.Some (vars, t)
         | uu____733 -> FStar_Pervasives_Native.None)
let (lookup_ty_const :
  uenv ->
    FStar_Extraction_ML_Syntax.mlpath ->
      FStar_Extraction_ML_Syntax.mltyscheme FStar_Pervasives_Native.option)
  =
  fun env ->
    fun uu____748 ->
      match uu____748 with
      | (module_name, ty_name) ->
          FStar_Util.find_map env.tydefs
            (fun tydef ->
               if
                 (module_name = tydef.tydef_mlmodule_name) &&
                   (ty_name = tydef.tydef_name)
               then FStar_Pervasives_Native.Some (tydef.tydef_def)
               else FStar_Pervasives_Native.None)
let (module_name_of_fv : FStar_Syntax_Syntax.fv -> Prims.string Prims.list) =
  fun fv ->
    FStar_All.pipe_right
      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ns
      (FStar_List.map (fun i -> i.FStar_Ident.idText))
let (maybe_mangle_type_projector :
  uenv ->
    FStar_Syntax_Syntax.fv ->
      FStar_Extraction_ML_Syntax.mlpath FStar_Pervasives_Native.option)
  =
  fun env ->
    fun fv ->
      let mname = module_name_of_fv fv in
      let ty_name =
        (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText in
      FStar_Util.find_map env.tydefs
        (fun tydef ->
           if
             (tydef.tydef_mlmodule_name = mname) &&
               (tydef.tydef_name = ty_name)
           then
             match tydef.tydef_mangled_name with
             | FStar_Pervasives_Native.None ->
                 FStar_Pervasives_Native.Some (mname, ty_name)
             | FStar_Pervasives_Native.Some mangled ->
                 FStar_Pervasives_Native.Some (mname, mangled)
           else FStar_Pervasives_Native.None)
let (lookup_tyvar :
  uenv -> FStar_Syntax_Syntax.bv -> FStar_Extraction_ML_Syntax.mlty) =
  fun g -> fun bt -> lookup_ty_local g.env_bindings bt
let (lookup_fv_by_lid : uenv -> FStar_Ident.lident -> ty_or_exp_b) =
  fun g ->
    fun lid ->
      let x =
        FStar_Util.find_map g.env_bindings
          (fun uu___0_913 ->
             match uu___0_913 with
             | Fv (fv', x) when FStar_Syntax_Syntax.fv_eq_lid fv' lid ->
                 FStar_Pervasives_Native.Some x
             | uu____918 -> FStar_Pervasives_Native.None) in
      match x with
      | FStar_Pervasives_Native.None ->
          let uu____919 =
            FStar_Util.format1 "free Variable %s not found\n"
              lid.FStar_Ident.nsstr in
          failwith uu____919
      | FStar_Pervasives_Native.Some y -> FStar_Util.Inr y
let (try_lookup_fv :
  uenv ->
    FStar_Syntax_Syntax.fv -> exp_binding FStar_Pervasives_Native.option)
  =
  fun g ->
    fun fv ->
      FStar_Util.find_map g.env_bindings
        (fun uu___1_941 ->
           match uu___1_941 with
           | Fv (fv', t) when FStar_Syntax_Syntax.fv_eq fv fv' ->
               FStar_Pervasives_Native.Some t
           | uu____946 -> FStar_Pervasives_Native.None)
let (lookup_fv : uenv -> FStar_Syntax_Syntax.fv -> exp_binding) =
  fun g ->
    fun fv ->
      let uu____958 = try_lookup_fv g fv in
      match uu____958 with
      | FStar_Pervasives_Native.None ->
          let uu____961 =
            let uu____963 =
              FStar_Range.string_of_range
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.p in
            let uu____965 =
              FStar_Syntax_Print.lid_to_string
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            FStar_Util.format2 "(%s) free Variable %s not found\n" uu____963
              uu____965 in
          failwith uu____961
      | FStar_Pervasives_Native.Some y -> y
let (lookup_bv : uenv -> FStar_Syntax_Syntax.bv -> ty_or_exp_b) =
  fun g ->
    fun bv ->
      let x =
        FStar_Util.find_map g.env_bindings
          (fun uu___2_986 ->
             match uu___2_986 with
             | Bv (bv', r) when FStar_Syntax_Syntax.bv_eq bv bv' ->
                 FStar_Pervasives_Native.Some r
             | uu____991 -> FStar_Pervasives_Native.None) in
      match x with
      | FStar_Pervasives_Native.None ->
          let uu____992 =
            let uu____994 =
              FStar_Range.string_of_range
                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange in
            let uu____996 = FStar_Syntax_Print.bv_to_string bv in
            FStar_Util.format2 "(%s) bound Variable %s not found\n" uu____994
              uu____996 in
          failwith uu____992
      | FStar_Pervasives_Native.Some y -> y
let (lookup :
  uenv ->
    (FStar_Syntax_Syntax.bv, FStar_Syntax_Syntax.fv) FStar_Util.either ->
      (ty_or_exp_b * FStar_Syntax_Syntax.fv_qual
        FStar_Pervasives_Native.option))
  =
  fun g ->
    fun x ->
      match x with
      | FStar_Util.Inl x1 ->
          let uu____1032 = lookup_bv g x1 in
          (uu____1032, FStar_Pervasives_Native.None)
      | FStar_Util.Inr x1 ->
          let uu____1036 =
            let uu____1037 = lookup_fv g x1 in FStar_Util.Inr uu____1037 in
          (uu____1036, (x1.FStar_Syntax_Syntax.fv_qual))
let (lookup_term :
  uenv ->
    FStar_Syntax_Syntax.term ->
      (ty_or_exp_b * FStar_Syntax_Syntax.fv_qual
        FStar_Pervasives_Native.option))
  =
  fun g ->
    fun t ->
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_name x -> lookup g (FStar_Util.Inl x)
      | FStar_Syntax_Syntax.Tm_fvar x -> lookup g (FStar_Util.Inr x)
      | uu____1065 -> failwith "Impossible: lookup_term for a non-name"
let (extend_ty :
  uenv ->
    FStar_Syntax_Syntax.bv ->
      FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option -> uenv)
  =
  fun g ->
    fun a ->
      fun mapped_to ->
        let ml_a = bv_as_ml_tyvar a in
        let mapped_to1 =
          match mapped_to with
          | FStar_Pervasives_Native.None ->
              FStar_Extraction_ML_Syntax.MLTY_Var ml_a
          | FStar_Pervasives_Native.Some t -> t in
        let gamma =
          (Bv
             (a, (FStar_Util.Inl { ty_b_name = ml_a; ty_b_ty = mapped_to1 })))
          :: (g.env_bindings) in
        let tcenv = FStar_TypeChecker_Env.push_bv g.env_tcenv a in
        let uu___200_1101 = g in
        {
          env_tcenv = tcenv;
          env_bindings = gamma;
          tydefs = (uu___200_1101.tydefs);
          type_names = (uu___200_1101.type_names);
          currentModule = (uu___200_1101.currentModule)
        }
let (sanitize : Prims.string -> Prims.string) =
  fun s ->
    let cs = FStar_String.list_of_string s in
    let valid c = ((FStar_Util.is_letter_or_digit c) || (c = 95)) || (c = 39) in
    let cs' =
      FStar_List.fold_right
        (fun c ->
           fun cs1 ->
             let uu____1146 =
               let uu____1150 = valid c in
               if uu____1150 then [c] else [95; 95] in
             FStar_List.append uu____1146 cs1) cs [] in
    let cs'1 =
      match cs' with
      | c::cs1 when (FStar_Util.is_digit c) || (c = 39) -> 95 :: c :: cs1
      | uu____1186 -> cs in
    FStar_String.string_of_list cs'1
let (find_uniq : binding Prims.list -> Prims.string -> Prims.string) =
  fun gamma ->
    fun mlident ->
      let rec find_uniq mlident1 i =
        let suffix =
          if i = (Prims.parse_int "0")
          then ""
          else FStar_Util.string_of_int i in
        let target_mlident = Prims.op_Hat mlident1 suffix in
        let has_collision =
          FStar_List.existsb
            (fun uu___3_1240 ->
               match uu___3_1240 with
               | Bv (uu____1242, FStar_Util.Inl ty_b) ->
                   target_mlident = ty_b.ty_b_name
               | Fv (uu____1245, exp_b) -> target_mlident = exp_b.exp_b_name
               | Bv (uu____1248, FStar_Util.Inr exp_b) ->
                   target_mlident = exp_b.exp_b_name) gamma in
        if has_collision
        then find_uniq mlident1 (i + (Prims.parse_int "1"))
        else target_mlident in
      let mlident1 = sanitize mlident in
      find_uniq mlident1 (Prims.parse_int "0")
let (extend_bv :
  uenv ->
    FStar_Syntax_Syntax.bv ->
      FStar_Extraction_ML_Syntax.mltyscheme ->
        Prims.bool ->
          Prims.bool ->
            Prims.bool ->
              (uenv * FStar_Extraction_ML_Syntax.mlident * exp_binding))
  =
  fun g ->
    fun x ->
      fun t_x ->
        fun add_unit ->
          fun is_rec ->
            fun mk_unit ->
              let ml_ty =
                match t_x with
                | ([], t) -> t
                | uu____1313 -> FStar_Extraction_ML_Syntax.MLTY_Top in
              let mlident =
                let uu____1316 = FStar_Extraction_ML_Syntax.bv_as_mlident x in
                find_uniq g.env_bindings uu____1316 in
              let mlx = FStar_Extraction_ML_Syntax.MLE_Var mlident in
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
                  else FStar_Extraction_ML_Syntax.with_ty ml_ty mlx in
              let t_x1 =
                if add_unit
                then FStar_Extraction_ML_Syntax.pop_unit t_x
                else t_x in
              let exp_binding =
                {
                  exp_b_name = mlident;
                  exp_b_expr = mlx1;
                  exp_b_tscheme = t_x1;
                  exp_b_inst_ok = is_rec
                } in
              let gamma = (Bv (x, (FStar_Util.Inr exp_binding))) ::
                (g.env_bindings) in
              let tcenv =
                let uu____1337 = FStar_Syntax_Syntax.binders_of_list [x] in
                FStar_TypeChecker_Env.push_binders g.env_tcenv uu____1337 in
              ((let uu___261_1340 = g in
                {
                  env_tcenv = tcenv;
                  env_bindings = gamma;
                  tydefs = (uu___261_1340.tydefs);
                  type_names = (uu___261_1340.type_names);
                  currentModule = (uu___261_1340.currentModule)
                }), mlident, exp_binding)
let rec (mltyFvars :
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlident Prims.list)
  =
  fun t ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Var x -> [x]
    | FStar_Extraction_ML_Syntax.MLTY_Fun (t1, f, t2) ->
        let uu____1360 = mltyFvars t1 in
        let uu____1364 = mltyFvars t2 in
        FStar_List.append uu____1360 uu____1364
    | FStar_Extraction_ML_Syntax.MLTY_Named (args, path) ->
        FStar_List.collect mltyFvars args
    | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
        FStar_List.collect mltyFvars ts
    | FStar_Extraction_ML_Syntax.MLTY_Top -> []
    | FStar_Extraction_ML_Syntax.MLTY_Erased -> []
let rec (subsetMlidents :
  FStar_Extraction_ML_Syntax.mlident Prims.list ->
    FStar_Extraction_ML_Syntax.mlident Prims.list -> Prims.bool)
  =
  fun la ->
    fun lb ->
      match la with
      | h::tla -> (FStar_List.contains h lb) && (subsetMlidents tla lb)
      | [] -> true
let (tySchemeIsClosed : FStar_Extraction_ML_Syntax.mltyscheme -> Prims.bool)
  =
  fun tys ->
    let uu____1425 = mltyFvars (FStar_Pervasives_Native.snd tys) in
    subsetMlidents uu____1425 (FStar_Pervasives_Native.fst tys)
let (extend_fv' :
  uenv ->
    FStar_Syntax_Syntax.fv ->
      FStar_Extraction_ML_Syntax.mlpath ->
        FStar_Extraction_ML_Syntax.mltyscheme ->
          Prims.bool ->
            Prims.bool ->
              (uenv * FStar_Extraction_ML_Syntax.mlident * exp_binding))
  =
  fun g ->
    fun x ->
      fun y ->
        fun t_x ->
          fun add_unit ->
            fun is_rec ->
              let uu____1478 = tySchemeIsClosed t_x in
              if uu____1478
              then
                let ml_ty =
                  match t_x with
                  | ([], t) -> t
                  | uu____1491 -> FStar_Extraction_ML_Syntax.MLTY_Top in
                let uu____1492 =
                  let uu____1498 = y in
                  match uu____1498 with
                  | (ns, i) ->
                      let mlsymbol =
                        FStar_Extraction_ML_Syntax.avoid_keyword i in
                      ((ns, mlsymbol), mlsymbol) in
                match uu____1492 with
                | (mlpath, mlsymbol) ->
                    let mly = FStar_Extraction_ML_Syntax.MLE_Name mlpath in
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
                      else FStar_Extraction_ML_Syntax.with_ty ml_ty mly in
                    let t_x1 =
                      if add_unit
                      then FStar_Extraction_ML_Syntax.pop_unit t_x
                      else t_x in
                    let exp_binding =
                      {
                        exp_b_name = mlsymbol;
                        exp_b_expr = mly1;
                        exp_b_tscheme = t_x1;
                        exp_b_inst_ok = is_rec
                      } in
                    let gamma = (Fv (x, exp_binding)) :: (g.env_bindings) in
                    ((let uu___312_1549 = g in
                      {
                        env_tcenv = (uu___312_1549.env_tcenv);
                        env_bindings = gamma;
                        tydefs = (uu___312_1549.tydefs);
                        type_names = (uu___312_1549.type_names);
                        currentModule = (uu___312_1549.currentModule)
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
  fun g ->
    fun x ->
      fun t_x ->
        fun add_unit ->
          fun is_rec ->
            let mlp =
              FStar_Extraction_ML_Syntax.mlpath_of_lident
                (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
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
  fun g ->
    fun l ->
      fun t ->
        fun t_x ->
          fun add_unit ->
            fun is_rec ->
              match l with
              | FStar_Util.Inl x -> extend_bv g x t_x add_unit is_rec false
              | FStar_Util.Inr f ->
                  let uu____1657 =
                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                      (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  (match uu____1657 with
                   | (p, y) -> extend_fv' g f (p, y) t_x add_unit is_rec)
let (extend_tydef :
  uenv ->
    FStar_Syntax_Syntax.fv ->
      FStar_Extraction_ML_Syntax.one_mltydecl -> (uenv * tydef))
  =
  fun g ->
    fun fv ->
      fun td ->
        let m = module_name_of_fv fv in
        let uu____1707 = td in
        match uu____1707 with
        | (_assumed, name, mangled, vars, metadata, body_opt) ->
            let tydef =
              let uu____1733 =
                let uu____1734 = tyscheme_of_td td in
                FStar_Option.get uu____1734 in
              {
                tydef_fv = fv;
                tydef_mlmodule_name = m;
                tydef_name = name;
                tydef_mangled_name = mangled;
                tydef_def = uu____1733
              } in
            ((let uu___345_1743 = g in
              {
                env_tcenv = (uu___345_1743.env_tcenv);
                env_bindings = (uu___345_1743.env_bindings);
                tydefs = (tydef :: (g.tydefs));
                type_names = (fv :: (g.type_names));
                currentModule = (uu___345_1743.currentModule)
              }), tydef)
let (extend_type_name : uenv -> FStar_Syntax_Syntax.fv -> uenv) =
  fun g ->
    fun fv ->
      let uu___349_1755 = g in
      {
        env_tcenv = (uu___349_1755.env_tcenv);
        env_bindings = (uu___349_1755.env_bindings);
        tydefs = (uu___349_1755.tydefs);
        type_names = (fv :: (g.type_names));
        currentModule = (uu___349_1755.currentModule)
      }
let (is_type_name : uenv -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun g ->
    fun fv ->
      FStar_All.pipe_right g.type_names
        (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq fv))
let (is_fv_type : uenv -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun g ->
    fun fv ->
      (is_type_name g fv) ||
        (FStar_All.pipe_right g.tydefs
           (FStar_Util.for_some
              (fun tydef -> FStar_Syntax_Syntax.fv_eq fv tydef.tydef_fv)))
let (emptyMlPath : FStar_Extraction_ML_Syntax.mlpath) = ([], "")
let (mkContext : FStar_TypeChecker_Env.env -> uenv) =
  fun e ->
    let env =
      {
        env_tcenv = e;
        env_bindings = [];
        tydefs = [];
        type_names = [];
        currentModule = emptyMlPath
      } in
    let a = "'a" in
    let failwith_ty =
      ([a],
        (FStar_Extraction_ML_Syntax.MLTY_Fun
           ((FStar_Extraction_ML_Syntax.MLTY_Named
               ([], (["Prims"], "string"))),
             FStar_Extraction_ML_Syntax.E_IMPURE,
             (FStar_Extraction_ML_Syntax.MLTY_Var a)))) in
    let uu____1822 =
      let uu____1830 =
        let uu____1831 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.failwith_lid
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
        FStar_Util.Inr uu____1831 in
      extend_lb env uu____1830 FStar_Syntax_Syntax.tun failwith_ty false
        false in
    match uu____1822 with | (g, uu____1835, uu____1836) -> g
let (monad_op_name :
  FStar_Syntax_Syntax.eff_decl ->
    Prims.string -> (FStar_Extraction_ML_Syntax.mlpath * FStar_Ident.lident))
  =
  fun ed ->
    fun nm ->
      let lid =
        let uu____1857 = FStar_Ident.id_of_text nm in
        FStar_Syntax_Util.mk_field_projector_name_from_ident
          ed.FStar_Syntax_Syntax.mname uu____1857 in
      let uu____1858 = FStar_Extraction_ML_Syntax.mlpath_of_lident lid in
      (uu____1858, lid)
let (action_name :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.action ->
      (FStar_Extraction_ML_Syntax.mlpath * FStar_Ident.lident))
  =
  fun ed ->
    fun a ->
      let nm =
        ((a.FStar_Syntax_Syntax.action_name).FStar_Ident.ident).FStar_Ident.idText in
      let module_name = (ed.FStar_Syntax_Syntax.mname).FStar_Ident.ns in
      let lid =
        let uu____1880 =
          let uu____1883 =
            let uu____1886 = FStar_Ident.id_of_text nm in [uu____1886] in
          FStar_List.append module_name uu____1883 in
        FStar_Ident.lid_of_ids uu____1880 in
      let uu____1887 = FStar_Extraction_ML_Syntax.mlpath_of_lident lid in
      (uu____1887, lid)
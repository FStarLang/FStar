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
  fun projectee  ->
    match projectee with | Bv _0 -> true | uu____56648 -> false
  
let (__proj__Bv__item___0 :
  binding -> (FStar_Syntax_Syntax.bv * ty_or_exp_b)) =
  fun projectee  -> match projectee with | Bv _0 -> _0 
let (uu___is_Fv : binding -> Prims.bool) =
  fun projectee  ->
    match projectee with | Fv _0 -> true | uu____56683 -> false
  
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
  tydefs: tydef Prims.list ;
  type_names: FStar_Syntax_Syntax.fv Prims.list ;
  currentModule: FStar_Extraction_ML_Syntax.mlpath }
let (__proj__Mkuenv__item__env_tcenv : uenv -> FStar_TypeChecker_Env.env) =
  fun projectee  ->
    match projectee with
    | { env_tcenv; env_bindings; tydefs; type_names; currentModule;_} ->
        env_tcenv
  
let (__proj__Mkuenv__item__env_bindings : uenv -> binding Prims.list) =
  fun projectee  ->
    match projectee with
    | { env_tcenv; env_bindings; tydefs; type_names; currentModule;_} ->
        env_bindings
  
let (__proj__Mkuenv__item__tydefs : uenv -> tydef Prims.list) =
  fun projectee  ->
    match projectee with
    | { env_tcenv; env_bindings; tydefs; type_names; currentModule;_} ->
        tydefs
  
let (__proj__Mkuenv__item__type_names :
  uenv -> FStar_Syntax_Syntax.fv Prims.list) =
  fun projectee  ->
    match projectee with
    | { env_tcenv; env_bindings; tydefs; type_names; currentModule;_} ->
        type_names
  
let (__proj__Mkuenv__item__currentModule :
  uenv -> FStar_Extraction_ML_Syntax.mlpath) =
  fun projectee  ->
    match projectee with
    | { env_tcenv; env_bindings; tydefs; type_names; currentModule;_} ->
        currentModule
  
let (debug : uenv -> (unit -> unit) -> unit) =
  fun g  ->
    fun f  ->
      let c = FStar_Extraction_ML_Syntax.string_of_mlpath g.currentModule  in
      let uu____56986 =
        FStar_Options.debug_at_level c (FStar_Options.Other "Extraction")  in
      if uu____56986 then f () else ()
  
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
           (uu____57017,("FStar"::"Ghost"::[],"erased")) -> true
       | FStar_Extraction_ML_Syntax.MLTY_Named
           (uu____57033,("FStar"::"Tactics"::"Effect"::[],"tactic")) ->
           let uu____57050 = FStar_Options.codegen ()  in
           uu____57050 <> (FStar_Pervasives_Native.Some FStar_Options.Plugin)
       | uu____57055 -> false)
  
let (unknownType : FStar_Extraction_ML_Syntax.mlty) =
  FStar_Extraction_ML_Syntax.MLTY_Top 
let (prependTick : Prims.string -> Prims.string) =
  fun x  -> if FStar_Util.starts_with x "'" then x else Prims.op_Hat "'A" x 
let (removeTick : Prims.string -> Prims.string) =
  fun x  ->
    if FStar_Util.starts_with x "'"
    then FStar_Util.substring_from x (Prims.parse_int "1")
    else x
  
let (convRange : FStar_Range.range -> Prims.int) =
  fun r  -> (Prims.parse_int "0") 
let (convIdent : FStar_Ident.ident -> FStar_Extraction_ML_Syntax.mlident) =
  fun id1  -> id1.FStar_Ident.idText 
let (bv_as_ml_tyvar : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun x  ->
    let uu____57112 = FStar_Extraction_ML_Syntax.bv_as_mlident x  in
    prependTick uu____57112
  
let (bv_as_ml_termvar : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun x  ->
    let uu____57121 = FStar_Extraction_ML_Syntax.bv_as_mlident x  in
    removeTick uu____57121
  
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
      | (Bv (b',FStar_Util.Inr uu____57147))::tl1 ->
          if FStar_Syntax_Syntax.bv_eq b b'
          then
            failwith
              (Prims.op_Hat "Type/Expr clash: "
                 (b.FStar_Syntax_Syntax.ppname).FStar_Ident.idText)
          else lookup_ty_local tl1 b
      | uu____57155::tl1 -> lookup_ty_local tl1 b
      | [] ->
          failwith
            (Prims.op_Hat "extraction: unbound type var "
               (b.FStar_Syntax_Syntax.ppname).FStar_Ident.idText)
  
let tyscheme_of_td :
  'Auu____57171 'Auu____57172 'Auu____57173 'Auu____57174 .
    ('Auu____57171 * 'Auu____57172 * 'Auu____57173 *
      FStar_Extraction_ML_Syntax.mlidents * 'Auu____57174 *
      FStar_Extraction_ML_Syntax.mltybody FStar_Pervasives_Native.option) ->
      FStar_Extraction_ML_Syntax.mltyscheme FStar_Pervasives_Native.option
  =
  fun uu____57195  ->
    match uu____57195 with
    | (uu____57210,uu____57211,uu____57212,vars,uu____57214,body_opt) ->
        (match body_opt with
         | FStar_Pervasives_Native.Some
             (FStar_Extraction_ML_Syntax.MLTD_Abbrev t) ->
             FStar_Pervasives_Native.Some (vars, t)
         | uu____57225 -> FStar_Pervasives_Native.None)
  
let (lookup_ty_const :
  uenv ->
    FStar_Extraction_ML_Syntax.mlpath ->
      FStar_Extraction_ML_Syntax.mltyscheme FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun uu____57240  ->
      match uu____57240 with
      | (module_name,ty_name) ->
          FStar_Util.find_map env.tydefs
            (fun tydef  ->
               if
                 (module_name = tydef.tydef_mlmodule_name) &&
                   (ty_name = tydef.tydef_name)
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
             (tydef.tydef_mlmodule_name = mname) &&
               (tydef.tydef_name = ty_name)
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
          (fun uu___526_57405  ->
             match uu___526_57405 with
             | Fv (fv',x) when FStar_Syntax_Syntax.fv_eq_lid fv' lid ->
                 FStar_Pervasives_Native.Some x
             | uu____57410 -> FStar_Pervasives_Native.None)
         in
      match x with
      | FStar_Pervasives_Native.None  ->
          let uu____57411 =
            FStar_Util.format1 "free Variable %s not found\n"
              lid.FStar_Ident.nsstr
             in
          failwith uu____57411
      | FStar_Pervasives_Native.Some y -> FStar_Util.Inr y
  
let (try_lookup_fv :
  uenv ->
    FStar_Syntax_Syntax.fv -> exp_binding FStar_Pervasives_Native.option)
  =
  fun g  ->
    fun fv  ->
      FStar_Util.find_map g.env_bindings
        (fun uu___527_57433  ->
           match uu___527_57433 with
           | Fv (fv',t) when FStar_Syntax_Syntax.fv_eq fv fv' ->
               FStar_Pervasives_Native.Some t
           | uu____57438 -> FStar_Pervasives_Native.None)
  
let (lookup_fv : uenv -> FStar_Syntax_Syntax.fv -> exp_binding) =
  fun g  ->
    fun fv  ->
      let uu____57450 = try_lookup_fv g fv  in
      match uu____57450 with
      | FStar_Pervasives_Native.None  ->
          let uu____57453 =
            let uu____57455 =
              FStar_Range.string_of_range
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.p
               in
            let uu____57457 =
              FStar_Syntax_Print.lid_to_string
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            FStar_Util.format2 "(%s) free Variable %s not found\n"
              uu____57455 uu____57457
             in
          failwith uu____57453
      | FStar_Pervasives_Native.Some y -> y
  
let (lookup_bv : uenv -> FStar_Syntax_Syntax.bv -> ty_or_exp_b) =
  fun g  ->
    fun bv  ->
      let x =
        FStar_Util.find_map g.env_bindings
          (fun uu___528_57478  ->
             match uu___528_57478 with
             | Bv (bv',r) when FStar_Syntax_Syntax.bv_eq bv bv' ->
                 FStar_Pervasives_Native.Some r
             | uu____57483 -> FStar_Pervasives_Native.None)
         in
      match x with
      | FStar_Pervasives_Native.None  ->
          let uu____57484 =
            let uu____57486 =
              FStar_Range.string_of_range
                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange
               in
            let uu____57488 = FStar_Syntax_Print.bv_to_string bv  in
            FStar_Util.format2 "(%s) bound Variable %s not found\n"
              uu____57486 uu____57488
             in
          failwith uu____57484
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
          let uu____57524 = lookup_bv g x1  in
          (uu____57524, FStar_Pervasives_Native.None)
      | FStar_Util.Inr x1 ->
          let uu____57528 =
            let uu____57529 = lookup_fv g x1  in FStar_Util.Inr uu____57529
             in
          (uu____57528, (x1.FStar_Syntax_Syntax.fv_qual))
  
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
      | uu____57557 -> failwith "Impossible: lookup_term for a non-name"
  
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
        let tcenv = FStar_TypeChecker_Env.push_bv g.env_tcenv a  in
        let uu___726_57593 = g  in
        {
          env_tcenv = tcenv;
          env_bindings = gamma;
          tydefs = (uu___726_57593.tydefs);
          type_names = (uu___726_57593.type_names);
          currentModule = (uu___726_57593.currentModule)
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
             let uu____57638 =
               let uu____57642 = valid c  in
               if uu____57642 then [c] else [95; 95]  in
             FStar_List.append uu____57638 cs1) cs []
       in
    let cs'1 =
      match cs' with
      | c::cs1 when (FStar_Util.is_digit c) || (c = 39) -> 95 :: c :: cs1
      | uu____57678 -> cs  in
    FStar_String.string_of_list cs'1
  
let (find_uniq : binding Prims.list -> Prims.string -> Prims.string) =
  fun gamma  ->
    fun mlident  ->
      let rec find_uniq mlident1 i =
        let suffix =
          if i = (Prims.parse_int "0")
          then ""
          else FStar_Util.string_of_int i  in
        let target_mlident = Prims.op_Hat mlident1 suffix  in
        let has_collision =
          FStar_List.existsb
            (fun uu___529_57732  ->
               match uu___529_57732 with
               | Bv (uu____57734,FStar_Util.Inl ty_b) ->
                   target_mlident = ty_b.ty_b_name
               | Fv (uu____57737,exp_b) -> target_mlident = exp_b.exp_b_name
               | Bv (uu____57740,FStar_Util.Inr exp_b) ->
                   target_mlident = exp_b.exp_b_name) gamma
           in
        if has_collision
        then find_uniq mlident1 (i + (Prims.parse_int "1"))
        else target_mlident  in
      let mlident1 = sanitize mlident  in
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
  fun g  ->
    fun x  ->
      fun t_x  ->
        fun add_unit  ->
          fun is_rec  ->
            fun mk_unit  ->
              let ml_ty =
                match t_x with
                | ([],t) -> t
                | uu____57805 -> FStar_Extraction_ML_Syntax.MLTY_Top  in
              let mlident =
                let uu____57808 = FStar_Extraction_ML_Syntax.bv_as_mlident x
                   in
                find_uniq g.env_bindings uu____57808  in
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
              let tcenv =
                let uu____57829 = FStar_Syntax_Syntax.binders_of_list [x]  in
                FStar_TypeChecker_Env.push_binders g.env_tcenv uu____57829
                 in
              ((let uu___787_57832 = g  in
                {
                  env_tcenv = tcenv;
                  env_bindings = gamma;
                  tydefs = (uu___787_57832.tydefs);
                  type_names = (uu___787_57832.type_names);
                  currentModule = (uu___787_57832.currentModule)
                }), mlident, exp_binding)
  
let rec (mltyFvars :
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlident Prims.list)
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Var x -> [x]
    | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,f,t2) ->
        let uu____57852 = mltyFvars t1  in
        let uu____57856 = mltyFvars t2  in
        FStar_List.append uu____57852 uu____57856
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
    let uu____57917 = mltyFvars (FStar_Pervasives_Native.snd tys)  in
    subsetMlidents uu____57917 (FStar_Pervasives_Native.fst tys)
  
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
              let uu____57970 = tySchemeIsClosed t_x  in
              if uu____57970
              then
                let ml_ty =
                  match t_x with
                  | ([],t) -> t
                  | uu____57983 -> FStar_Extraction_ML_Syntax.MLTY_Top  in
                let uu____57984 =
                  let uu____57990 = y  in
                  match uu____57990 with
                  | (ns,i) ->
                      let mlsymbol =
                        FStar_Extraction_ML_Syntax.avoid_keyword i  in
                      ((ns, mlsymbol), mlsymbol)
                   in
                match uu____57984 with
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
                    ((let uu___838_58041 = g  in
                      {
                        env_tcenv = (uu___838_58041.env_tcenv);
                        env_bindings = gamma;
                        tydefs = (uu___838_58041.tydefs);
                        type_names = (uu___838_58041.type_names);
                        currentModule = (uu___838_58041.currentModule)
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
                  let uu____58149 =
                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                      (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                     in
                  (match uu____58149 with
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
        let uu____58199 = td  in
        match uu____58199 with
        | (_assumed,name,mangled,vars,metadata,body_opt) ->
            let tydef =
              let uu____58225 =
                let uu____58226 = tyscheme_of_td td  in
                FStar_Option.get uu____58226  in
              {
                tydef_fv = fv;
                tydef_mlmodule_name = m;
                tydef_name = name;
                tydef_mangled_name = mangled;
                tydef_def = uu____58225
              }  in
            ((let uu___871_58235 = g  in
              {
                env_tcenv = (uu___871_58235.env_tcenv);
                env_bindings = (uu___871_58235.env_bindings);
                tydefs = (tydef :: (g.tydefs));
                type_names = (fv :: (g.type_names));
                currentModule = (uu___871_58235.currentModule)
              }), tydef)
  
let (extend_type_name : uenv -> FStar_Syntax_Syntax.fv -> uenv) =
  fun g  ->
    fun fv  ->
      let uu___875_58247 = g  in
      {
        env_tcenv = (uu___875_58247.env_tcenv);
        env_bindings = (uu___875_58247.env_bindings);
        tydefs = (uu___875_58247.tydefs);
        type_names = (fv :: (g.type_names));
        currentModule = (uu___875_58247.currentModule)
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
      {
        env_tcenv = e;
        env_bindings = [];
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
    let uu____58314 =
      let uu____58322 =
        let uu____58323 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.failwith_lid
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        FStar_Util.Inr uu____58323  in
      extend_lb env uu____58322 FStar_Syntax_Syntax.tun failwith_ty false
        false
       in
    match uu____58314 with | (g,uu____58327,uu____58328) -> g
  
let (monad_op_name :
  FStar_Syntax_Syntax.eff_decl ->
    Prims.string -> (FStar_Extraction_ML_Syntax.mlpath * FStar_Ident.lident))
  =
  fun ed  ->
    fun nm  ->
      let lid =
        let uu____58349 = FStar_Ident.id_of_text nm  in
        FStar_Syntax_Util.mk_field_projector_name_from_ident
          ed.FStar_Syntax_Syntax.mname uu____58349
         in
      let uu____58350 = FStar_Extraction_ML_Syntax.mlpath_of_lident lid  in
      (uu____58350, lid)
  
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
        let uu____58372 =
          let uu____58375 =
            let uu____58378 = FStar_Ident.id_of_text nm  in [uu____58378]  in
          FStar_List.append module_name uu____58375  in
        FStar_Ident.lid_of_ids uu____58372  in
      let uu____58379 = FStar_Extraction_ML_Syntax.mlpath_of_lident lid  in
      (uu____58379, lid)
  
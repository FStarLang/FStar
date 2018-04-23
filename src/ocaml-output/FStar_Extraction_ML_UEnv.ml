open Prims
type ty_or_exp_b =
  ((FStar_Extraction_ML_Syntax.mlident,FStar_Extraction_ML_Syntax.mlty)
     FStar_Pervasives_Native.tuple2,(FStar_Extraction_ML_Syntax.mlsymbol,
                                      FStar_Extraction_ML_Syntax.mlexpr,
                                      FStar_Extraction_ML_Syntax.mltyscheme,
                                      Prims.bool)
                                      FStar_Pervasives_Native.tuple4)
    FStar_Util.either[@@deriving show]
type binding =
  | Bv of (FStar_Syntax_Syntax.bv,ty_or_exp_b) FStar_Pervasives_Native.tuple2
  
  | Fv of (FStar_Syntax_Syntax.fv,ty_or_exp_b) FStar_Pervasives_Native.tuple2 
[@@deriving show]
let uu___is_Bv : binding -> Prims.bool =
  fun projectee  -> match projectee with | Bv _0 -> true | uu____45 -> false 
let __proj__Bv__item___0 :
  binding ->
    (FStar_Syntax_Syntax.bv,ty_or_exp_b) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Bv _0 -> _0 
let uu___is_Fv : binding -> Prims.bool =
  fun projectee  -> match projectee with | Fv _0 -> true | uu____75 -> false 
let __proj__Fv__item___0 :
  binding ->
    (FStar_Syntax_Syntax.fv,ty_or_exp_b) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Fv _0 -> _0 
type env =
  {
  tcenv: FStar_TypeChecker_Env.env ;
  gamma: binding Prims.list ;
  tydefs:
    (FStar_Syntax_Syntax.fv,FStar_Extraction_ML_Syntax.mlsymbol Prims.list,
      FStar_Extraction_ML_Syntax.mltydecl) FStar_Pervasives_Native.tuple3
      Prims.list
    ;
  type_names: FStar_Syntax_Syntax.fv Prims.list ;
  currentModule: FStar_Extraction_ML_Syntax.mlpath }[@@deriving show]
let __proj__Mkenv__item__tcenv : env -> FStar_TypeChecker_Env.env =
  fun projectee  ->
    match projectee with
    | { tcenv = __fname__tcenv; gamma = __fname__gamma;
        tydefs = __fname__tydefs; type_names = __fname__type_names;
        currentModule = __fname__currentModule;_} -> __fname__tcenv
  
let __proj__Mkenv__item__gamma : env -> binding Prims.list =
  fun projectee  ->
    match projectee with
    | { tcenv = __fname__tcenv; gamma = __fname__gamma;
        tydefs = __fname__tydefs; type_names = __fname__type_names;
        currentModule = __fname__currentModule;_} -> __fname__gamma
  
let __proj__Mkenv__item__tydefs :
  env ->
    (FStar_Syntax_Syntax.fv,FStar_Extraction_ML_Syntax.mlsymbol Prims.list,
      FStar_Extraction_ML_Syntax.mltydecl) FStar_Pervasives_Native.tuple3
      Prims.list
  =
  fun projectee  ->
    match projectee with
    | { tcenv = __fname__tcenv; gamma = __fname__gamma;
        tydefs = __fname__tydefs; type_names = __fname__type_names;
        currentModule = __fname__currentModule;_} -> __fname__tydefs
  
let __proj__Mkenv__item__type_names :
  env -> FStar_Syntax_Syntax.fv Prims.list =
  fun projectee  ->
    match projectee with
    | { tcenv = __fname__tcenv; gamma = __fname__gamma;
        tydefs = __fname__tydefs; type_names = __fname__type_names;
        currentModule = __fname__currentModule;_} -> __fname__type_names
  
let __proj__Mkenv__item__currentModule :
  env -> FStar_Extraction_ML_Syntax.mlpath =
  fun projectee  ->
    match projectee with
    | { tcenv = __fname__tcenv; gamma = __fname__gamma;
        tydefs = __fname__tydefs; type_names = __fname__type_names;
        currentModule = __fname__currentModule;_} -> __fname__currentModule
  
let debug : env -> (unit -> unit) -> unit =
  fun g  ->
    fun f  ->
      let c = FStar_Extraction_ML_Syntax.string_of_mlpath g.currentModule  in
      let uu____298 =
        FStar_Options.debug_at_level c (FStar_Options.Other "Extraction")  in
      if uu____298 then f () else ()
  
let mkFvvar :
  FStar_Ident.lident -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.fv =
  fun l  ->
    fun t  ->
      FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
        FStar_Pervasives_Native.None
  
let erasedContent : FStar_Extraction_ML_Syntax.mlty =
  FStar_Extraction_ML_Syntax.MLTY_Erased 
let erasableTypeNoDelta : FStar_Extraction_ML_Syntax.mlty -> Prims.bool =
  fun t  ->
    if t = FStar_Extraction_ML_Syntax.ml_unit_ty
    then true
    else
      (match t with
       | FStar_Extraction_ML_Syntax.MLTY_Named
           (uu____316,("FStar"::"Ghost"::[],"erased")) -> true
       | FStar_Extraction_ML_Syntax.MLTY_Named
           (uu____329,("FStar"::"Tactics"::"Effect"::[],"tactic")) ->
           let uu____342 = FStar_Options.codegen ()  in
           uu____342 <> (FStar_Pervasives_Native.Some FStar_Options.Plugin)
       | uu____347 -> false)
  
let unknownType : FStar_Extraction_ML_Syntax.mlty =
  FStar_Extraction_ML_Syntax.MLTY_Top 
let prependTick : Prims.string -> Prims.string =
  fun x  -> if FStar_Util.starts_with x "'" then x else Prims.strcat "'A" x 
let removeTick : Prims.string -> Prims.string =
  fun x  ->
    if FStar_Util.starts_with x "'"
    then FStar_Util.substring_from x (Prims.lift_native_int (1))
    else x
  
let convRange : FStar_Range.range -> Prims.int =
  fun r  -> (Prims.lift_native_int (0)) 
let convIdent : FStar_Ident.ident -> FStar_Extraction_ML_Syntax.mlident =
  fun id1  -> id1.FStar_Ident.idText 
let bv_as_ml_tyvar : FStar_Syntax_Syntax.bv -> Prims.string =
  fun x  ->
    let uu____375 = FStar_Extraction_ML_Syntax.bv_as_mlident x  in
    prependTick uu____375
  
let bv_as_ml_termvar : FStar_Syntax_Syntax.bv -> Prims.string =
  fun x  ->
    let uu____381 = FStar_Extraction_ML_Syntax.bv_as_mlident x  in
    removeTick uu____381
  
let rec lookup_ty_local :
  binding Prims.list ->
    FStar_Syntax_Syntax.bv -> FStar_Extraction_ML_Syntax.mlty
  =
  fun gamma  ->
    fun b  ->
      match gamma with
      | (Bv (b',FStar_Util.Inl (mli,mlt)))::tl1 ->
          if FStar_Syntax_Syntax.bv_eq b b'
          then mlt
          else lookup_ty_local tl1 b
      | (Bv (b',FStar_Util.Inr uu____432))::tl1 ->
          if FStar_Syntax_Syntax.bv_eq b b'
          then
            failwith
              (Prims.strcat "Type/Expr clash: "
                 (b.FStar_Syntax_Syntax.ppname).FStar_Ident.idText)
          else lookup_ty_local tl1 b
      | uu____473::tl1 -> lookup_ty_local tl1 b
      | [] ->
          failwith
            (Prims.strcat "extraction: unbound type var "
               (b.FStar_Syntax_Syntax.ppname).FStar_Ident.idText)
  
let tyscheme_of_td :
  'Auu____487 'Auu____488 'Auu____489 'Auu____490 .
    ('Auu____487,'Auu____488,'Auu____489,FStar_Extraction_ML_Syntax.mlidents,
      'Auu____490,FStar_Extraction_ML_Syntax.mltybody
                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple6 ->
      FStar_Extraction_ML_Syntax.mltyscheme FStar_Pervasives_Native.option
  =
  fun uu____511  ->
    match uu____511 with
    | (uu____526,uu____527,uu____528,vars,uu____530,body_opt) ->
        (match body_opt with
         | FStar_Pervasives_Native.Some
             (FStar_Extraction_ML_Syntax.MLTD_Abbrev t) ->
             FStar_Pervasives_Native.Some (vars, t)
         | uu____545 -> FStar_Pervasives_Native.None)
  
let lookup_ty_const :
  env ->
    FStar_Extraction_ML_Syntax.mlpath ->
      FStar_Extraction_ML_Syntax.mltyscheme FStar_Pervasives_Native.option
  =
  fun env  ->
    fun uu____559  ->
      match uu____559 with
      | (module_name,ty_name) ->
          FStar_Util.find_map env.tydefs
            (fun uu____582  ->
               match uu____582 with
               | (uu____593,m,tds) ->
                   if module_name = m
                   then
                     FStar_Util.find_map tds
                       (fun td  ->
                          let uu____613 = td  in
                          match uu____613 with
                          | (uu____616,n1,uu____618,uu____619,uu____620,uu____621)
                              ->
                              if n1 = ty_name
                              then tyscheme_of_td td
                              else FStar_Pervasives_Native.None)
                   else FStar_Pervasives_Native.None)
  
let module_name_of_fv : FStar_Syntax_Syntax.fv -> Prims.string Prims.list =
  fun fv  ->
    FStar_All.pipe_right
      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ns
      (FStar_List.map (fun i  -> i.FStar_Ident.idText))
  
let maybe_mangle_type_projector :
  env ->
    FStar_Syntax_Syntax.fv ->
      FStar_Extraction_ML_Syntax.mlpath FStar_Pervasives_Native.option
  =
  fun env  ->
    fun fv  ->
      let mname = module_name_of_fv fv  in
      let ty_name =
        (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText
         in
      FStar_Util.find_map env.tydefs
        (fun uu____685  ->
           match uu____685 with
           | (uu____702,m,tds) ->
               FStar_Util.find_map tds
                 (fun uu____722  ->
                    match uu____722 with
                    | (uu____731,n1,mangle_opt,uu____734,uu____735,uu____736)
                        ->
                        if m = mname
                        then
                          (if n1 = ty_name
                           then
                             match mangle_opt with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.Some (m, n1)
                             | FStar_Pervasives_Native.Some mangled ->
                                 let modul = m  in
                                 FStar_Pervasives_Native.Some
                                   (modul, mangled)
                           else FStar_Pervasives_Native.None)
                        else FStar_Pervasives_Native.None))
  
let lookup_tyvar :
  env -> FStar_Syntax_Syntax.bv -> FStar_Extraction_ML_Syntax.mlty =
  fun g  -> fun bt  -> lookup_ty_local g.gamma bt 
let lookup_fv_by_lid : env -> FStar_Ident.lident -> ty_or_exp_b =
  fun g  ->
    fun lid  ->
      let x =
        FStar_Util.find_map g.gamma
          (fun uu___57_831  ->
             match uu___57_831 with
             | Fv (fv',x) when FStar_Syntax_Syntax.fv_eq_lid fv' lid ->
                 FStar_Pervasives_Native.Some x
             | uu____836 -> FStar_Pervasives_Native.None)
         in
      match x with
      | FStar_Pervasives_Native.None  ->
          let uu____837 =
            FStar_Util.format1 "free Variable %s not found\n"
              lid.FStar_Ident.nsstr
             in
          failwith uu____837
      | FStar_Pervasives_Native.Some y -> y
  
let try_lookup_fv :
  env -> FStar_Syntax_Syntax.fv -> ty_or_exp_b FStar_Pervasives_Native.option
  =
  fun g  ->
    fun fv  ->
      FStar_Util.find_map g.gamma
        (fun uu___58_856  ->
           match uu___58_856 with
           | Fv (fv',t) when FStar_Syntax_Syntax.fv_eq fv fv' ->
               FStar_Pervasives_Native.Some t
           | uu____861 -> FStar_Pervasives_Native.None)
  
let lookup_fv : env -> FStar_Syntax_Syntax.fv -> ty_or_exp_b =
  fun g  ->
    fun fv  ->
      let uu____872 = try_lookup_fv g fv  in
      match uu____872 with
      | FStar_Pervasives_Native.None  ->
          let uu____875 =
            let uu____876 =
              FStar_Range.string_of_range
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.p
               in
            let uu____877 =
              FStar_Syntax_Print.lid_to_string
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            FStar_Util.format2 "(%s) free Variable %s not found\n" uu____876
              uu____877
             in
          failwith uu____875
      | FStar_Pervasives_Native.Some y -> y
  
let lookup_bv : env -> FStar_Syntax_Syntax.bv -> ty_or_exp_b =
  fun g  ->
    fun bv  ->
      let x =
        FStar_Util.find_map g.gamma
          (fun uu___59_895  ->
             match uu___59_895 with
             | Bv (bv',r) when FStar_Syntax_Syntax.bv_eq bv bv' ->
                 FStar_Pervasives_Native.Some r
             | uu____900 -> FStar_Pervasives_Native.None)
         in
      match x with
      | FStar_Pervasives_Native.None  ->
          let uu____901 =
            let uu____902 =
              FStar_Range.string_of_range
                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange
               in
            let uu____903 = FStar_Syntax_Print.bv_to_string bv  in
            FStar_Util.format2 "(%s) bound Variable %s not found\n" uu____902
              uu____903
             in
          failwith uu____901
      | FStar_Pervasives_Native.Some y -> y
  
let lookup :
  env ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
      (ty_or_exp_b,FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2
  =
  fun g  ->
    fun x  ->
      match x with
      | FStar_Util.Inl x1 ->
          let uu____936 = lookup_bv g x1  in
          (uu____936, FStar_Pervasives_Native.None)
      | FStar_Util.Inr x1 ->
          let uu____940 = lookup_fv g x1  in
          (uu____940, (x1.FStar_Syntax_Syntax.fv_qual))
  
let lookup_term :
  env ->
    FStar_Syntax_Syntax.term ->
      (ty_or_exp_b,FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2
  =
  fun g  ->
    fun t  ->
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_name x -> lookup g (FStar_Util.Inl x)
      | FStar_Syntax_Syntax.Tm_fvar x -> lookup g (FStar_Util.Inr x)
      | uu____967 -> failwith "Impossible: lookup_term for a non-name"
  
let extend_ty :
  env ->
    FStar_Syntax_Syntax.bv ->
      FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option -> env
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
        let gamma = (Bv (a, (FStar_Util.Inl (ml_a, mapped_to1)))) ::
          (g.gamma)  in
        let tcenv = FStar_TypeChecker_Env.push_bv g.tcenv a  in
        let uu___61_1028 = g  in
        {
          tcenv;
          gamma;
          tydefs = (uu___61_1028.tydefs);
          type_names = (uu___61_1028.type_names);
          currentModule = (uu___61_1028.currentModule)
        }
  
let sanitize : Prims.string -> Prims.string =
  fun s  ->
    let cs = FStar_String.list_of_string s  in
    let valid c = ((FStar_Util.is_letter_or_digit c) || (c = 95)) || (c = 39)
       in
    let cs' =
      FStar_List.fold_right
        (fun c  ->
           fun cs1  ->
             let uu____1058 =
               let uu____1061 = valid c  in
               if uu____1061 then [c] else [95; 95]  in
             FStar_List.append uu____1058 cs1) cs []
       in
    let cs'1 =
      match cs' with
      | c::cs1 when (FStar_Util.is_digit c) || (c = 39) -> 95 :: c :: cs1
      | uu____1084 -> cs  in
    FStar_String.string_of_list cs'1
  
let find_uniq : binding Prims.list -> Prims.string -> Prims.string =
  fun gamma  ->
    fun mlident  ->
      let rec find_uniq mlident1 i =
        let suffix =
          if i = (Prims.lift_native_int (0))
          then ""
          else FStar_Util.string_of_int i  in
        let target_mlident = Prims.strcat mlident1 suffix  in
        let has_collision =
          FStar_List.existsb
            (fun uu___60_1120  ->
               match uu___60_1120 with
               | Bv (uu____1121,FStar_Util.Inl (mlident',uu____1123)) ->
                   target_mlident = mlident'
               | Fv (uu____1152,FStar_Util.Inl (mlident',uu____1154)) ->
                   target_mlident = mlident'
               | Fv
                   (uu____1183,FStar_Util.Inr
                    (mlident',uu____1185,uu____1186,uu____1187))
                   -> target_mlident = mlident'
               | Bv
                   (uu____1216,FStar_Util.Inr
                    (mlident',uu____1218,uu____1219,uu____1220))
                   -> target_mlident = mlident') gamma
           in
        if has_collision
        then find_uniq mlident1 (i + (Prims.lift_native_int (1)))
        else target_mlident  in
      let mlident1 = sanitize mlident  in
      find_uniq mlident1 (Prims.lift_native_int (0))
  
let extend_bv :
  env ->
    FStar_Syntax_Syntax.bv ->
      FStar_Extraction_ML_Syntax.mltyscheme ->
        Prims.bool ->
          Prims.bool ->
            Prims.bool ->
              (env,FStar_Extraction_ML_Syntax.mlident)
                FStar_Pervasives_Native.tuple2
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
                | uu____1293 -> FStar_Extraction_ML_Syntax.MLTY_Top  in
              let mlident =
                let uu____1295 = FStar_Extraction_ML_Syntax.bv_as_mlident x
                   in
                find_uniq g.gamma uu____1295  in
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
              let gamma =
                (Bv (x, (FStar_Util.Inr (mlident, mlx1, t_x1, is_rec)))) ::
                (g.gamma)  in
              let tcenv =
                let uu____1336 = FStar_Syntax_Syntax.binders_of_list [x]  in
                FStar_TypeChecker_Env.push_binders g.tcenv uu____1336  in
              ((let uu___62_1338 = g  in
                {
                  tcenv;
                  gamma;
                  tydefs = (uu___62_1338.tydefs);
                  type_names = (uu___62_1338.type_names);
                  currentModule = (uu___62_1338.currentModule)
                }), mlident)
  
let rec mltyFvars :
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlident Prims.list
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Var x -> [x]
    | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,f,t2) ->
        let uu____1352 = mltyFvars t1  in
        let uu____1355 = mltyFvars t2  in
        FStar_List.append uu____1352 uu____1355
    | FStar_Extraction_ML_Syntax.MLTY_Named (args,path) ->
        FStar_List.collect mltyFvars args
    | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
        FStar_List.collect mltyFvars ts
    | FStar_Extraction_ML_Syntax.MLTY_Top  -> []
    | FStar_Extraction_ML_Syntax.MLTY_Erased  -> []
  
let rec subsetMlidents :
  FStar_Extraction_ML_Syntax.mlident Prims.list ->
    FStar_Extraction_ML_Syntax.mlident Prims.list -> Prims.bool
  =
  fun la  ->
    fun lb  ->
      match la with
      | h::tla -> (FStar_List.contains h lb) && (subsetMlidents tla lb)
      | [] -> true
  
let tySchemeIsClosed : FStar_Extraction_ML_Syntax.mltyscheme -> Prims.bool =
  fun tys  ->
    let uu____1394 = mltyFvars (FStar_Pervasives_Native.snd tys)  in
    subsetMlidents uu____1394 (FStar_Pervasives_Native.fst tys)
  
let extend_fv' :
  env ->
    FStar_Syntax_Syntax.fv ->
      FStar_Extraction_ML_Syntax.mlpath ->
        FStar_Extraction_ML_Syntax.mltyscheme ->
          Prims.bool ->
            Prims.bool ->
              (env,FStar_Extraction_ML_Syntax.mlident)
                FStar_Pervasives_Native.tuple2
  =
  fun g  ->
    fun x  ->
      fun y  ->
        fun t_x  ->
          fun add_unit  ->
            fun is_rec  ->
              let uu____1435 = tySchemeIsClosed t_x  in
              if uu____1435
              then
                let ml_ty =
                  match t_x with
                  | ([],t) -> t
                  | uu____1444 -> FStar_Extraction_ML_Syntax.MLTY_Top  in
                let uu____1445 =
                  let uu____1456 = y  in
                  match uu____1456 with
                  | (ns,i) ->
                      let mlsymbol =
                        FStar_Extraction_ML_Syntax.avoid_keyword i  in
                      ((ns, mlsymbol), mlsymbol)
                   in
                match uu____1445 with
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
                    let gamma =
                      (Fv
                         (x, (FStar_Util.Inr (mlsymbol, mly1, t_x1, is_rec))))
                      :: (g.gamma)  in
                    ((let uu___63_1539 = g  in
                      {
                        tcenv = (uu___63_1539.tcenv);
                        gamma;
                        tydefs = (uu___63_1539.tydefs);
                        type_names = (uu___63_1539.type_names);
                        currentModule = (uu___63_1539.currentModule)
                      }), mlsymbol)
              else failwith "freevars found"
  
let extend_fv :
  env ->
    FStar_Syntax_Syntax.fv ->
      FStar_Extraction_ML_Syntax.mltyscheme ->
        Prims.bool ->
          Prims.bool ->
            (env,FStar_Extraction_ML_Syntax.mlident)
              FStar_Pervasives_Native.tuple2
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
  
let extend_lb :
  env ->
    FStar_Syntax_Syntax.lbname ->
      FStar_Syntax_Syntax.typ ->
        FStar_Extraction_ML_Syntax.mltyscheme ->
          Prims.bool ->
            Prims.bool ->
              (env,FStar_Extraction_ML_Syntax.mlident)
                FStar_Pervasives_Native.tuple2
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
                  let uu____1619 =
                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                      (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                     in
                  (match uu____1619 with
                   | (p,y) -> extend_fv' g f (p, y) t_x add_unit is_rec)
  
let extend_tydef :
  env -> FStar_Syntax_Syntax.fv -> FStar_Extraction_ML_Syntax.mltydecl -> env
  =
  fun g  ->
    fun fv  ->
      fun td  ->
        let m = module_name_of_fv fv  in
        let uu___64_1650 = g  in
        {
          tcenv = (uu___64_1650.tcenv);
          gamma = (uu___64_1650.gamma);
          tydefs = ((fv, m, td) :: (g.tydefs));
          type_names = (fv :: (g.type_names));
          currentModule = (uu___64_1650.currentModule)
        }
  
let extend_type_name : env -> FStar_Syntax_Syntax.fv -> env =
  fun g  ->
    fun fv  ->
      let uu___65_1671 = g  in
      {
        tcenv = (uu___65_1671.tcenv);
        gamma = (uu___65_1671.gamma);
        tydefs = (uu___65_1671.tydefs);
        type_names = (fv :: (g.type_names));
        currentModule = (uu___65_1671.currentModule)
      }
  
let is_type_name : env -> FStar_Syntax_Syntax.fv -> Prims.bool =
  fun g  ->
    fun fv  ->
      FStar_All.pipe_right g.type_names
        (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq fv))
  
let is_fv_type : env -> FStar_Syntax_Syntax.fv -> Prims.bool =
  fun g  ->
    fun fv  ->
      (is_type_name g fv) ||
        (FStar_All.pipe_right g.tydefs
           (FStar_Util.for_some
              (fun uu____1716  ->
                 match uu____1716 with
                 | (fv',uu____1726,uu____1727) ->
                     FStar_Syntax_Syntax.fv_eq fv fv')))
  
let emptyMlPath :
  (FStar_Extraction_ML_Syntax.mlsymbol Prims.list,Prims.string)
    FStar_Pervasives_Native.tuple2
  = ([], "") 
let mkContext : FStar_TypeChecker_Env.env -> env =
  fun e  ->
    let env =
      {
        tcenv = e;
        gamma = [];
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
    let uu____1774 =
      let uu____1779 =
        let uu____1780 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.failwith_lid
            FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
           in
        FStar_Util.Inr uu____1780  in
      extend_lb env uu____1779 FStar_Syntax_Syntax.tun failwith_ty false
        false
       in
    FStar_All.pipe_right uu____1774 FStar_Pervasives_Native.fst
  
let monad_op_name :
  FStar_Syntax_Syntax.eff_decl ->
    Prims.string ->
      (FStar_Extraction_ML_Syntax.mlpath,FStar_Ident.lident)
        FStar_Pervasives_Native.tuple2
  =
  fun ed  ->
    fun nm  ->
      let lid =
        let uu____1800 = FStar_Ident.id_of_text nm  in
        FStar_Syntax_Util.mk_field_projector_name_from_ident
          ed.FStar_Syntax_Syntax.mname uu____1800
         in
      let uu____1801 = FStar_Extraction_ML_Syntax.mlpath_of_lident lid  in
      (uu____1801, lid)
  
let action_name :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.action ->
      (FStar_Extraction_ML_Syntax.mlpath,FStar_Ident.lident)
        FStar_Pervasives_Native.tuple2
  =
  fun ed  ->
    fun a  ->
      let nm =
        ((a.FStar_Syntax_Syntax.action_name).FStar_Ident.ident).FStar_Ident.idText
         in
      let module_name = (ed.FStar_Syntax_Syntax.mname).FStar_Ident.ns  in
      let lid =
        let uu____1821 =
          let uu____1824 =
            let uu____1827 = FStar_Ident.id_of_text nm  in [uu____1827]  in
          FStar_List.append module_name uu____1824  in
        FStar_Ident.lid_of_ids uu____1821  in
      let uu____1828 = FStar_Extraction_ML_Syntax.mlpath_of_lident lid  in
      (uu____1828, lid)
  
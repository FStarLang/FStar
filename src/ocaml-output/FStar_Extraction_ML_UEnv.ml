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
let (uu___is_Bv : binding -> Prims.bool) =
  fun projectee  -> match projectee with | Bv _0 -> true | uu____41 -> false 
let (__proj__Bv__item___0 :
  binding ->
    (FStar_Syntax_Syntax.bv,ty_or_exp_b) FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Bv _0 -> _0 
let (uu___is_Fv : binding -> Prims.bool) =
  fun projectee  -> match projectee with | Fv _0 -> true | uu____69 -> false 
let (__proj__Fv__item___0 :
  binding ->
    (FStar_Syntax_Syntax.fv,ty_or_exp_b) FStar_Pervasives_Native.tuple2)
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
let (__proj__Mkenv__item__tcenv : env -> FStar_TypeChecker_Env.env) =
  fun projectee  ->
    match projectee with
    | { tcenv = __fname__tcenv; gamma = __fname__gamma;
        tydefs = __fname__tydefs; type_names = __fname__type_names;
        currentModule = __fname__currentModule;_} -> __fname__tcenv
  
let (__proj__Mkenv__item__gamma : env -> binding Prims.list) =
  fun projectee  ->
    match projectee with
    | { tcenv = __fname__tcenv; gamma = __fname__gamma;
        tydefs = __fname__tydefs; type_names = __fname__type_names;
        currentModule = __fname__currentModule;_} -> __fname__gamma
  
let (__proj__Mkenv__item__tydefs :
  env ->
    (FStar_Syntax_Syntax.fv,FStar_Extraction_ML_Syntax.mlsymbol Prims.list,
      FStar_Extraction_ML_Syntax.mltydecl) FStar_Pervasives_Native.tuple3
      Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { tcenv = __fname__tcenv; gamma = __fname__gamma;
        tydefs = __fname__tydefs; type_names = __fname__type_names;
        currentModule = __fname__currentModule;_} -> __fname__tydefs
  
let (__proj__Mkenv__item__type_names :
  env -> FStar_Syntax_Syntax.fv Prims.list) =
  fun projectee  ->
    match projectee with
    | { tcenv = __fname__tcenv; gamma = __fname__gamma;
        tydefs = __fname__tydefs; type_names = __fname__type_names;
        currentModule = __fname__currentModule;_} -> __fname__type_names
  
let (__proj__Mkenv__item__currentModule :
  env -> FStar_Extraction_ML_Syntax.mlpath) =
  fun projectee  ->
    match projectee with
    | { tcenv = __fname__tcenv; gamma = __fname__gamma;
        tydefs = __fname__tydefs; type_names = __fname__type_names;
        currentModule = __fname__currentModule;_} -> __fname__currentModule
  
let (debug : env -> (Prims.unit -> Prims.unit) -> Prims.unit) =
  fun g  ->
    fun f  ->
      let c = FStar_Extraction_ML_Syntax.string_of_mlpath g.currentModule  in
      let uu____273 =
        FStar_Options.debug_at_level c (FStar_Options.Other "Extraction")  in
      if uu____273 then f () else ()
  
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
           (uu____285,("FStar"::"Ghost"::[],"erased")) -> true
       | FStar_Extraction_ML_Syntax.MLTY_Named
           (uu____298,("FStar"::"Tactics"::"Effect"::[],"tactic")) ->
           let uu____311 = FStar_Options.codegen ()  in
           uu____311 <> (FStar_Pervasives_Native.Some FStar_Options.Plugin)
       | uu____316 -> false)
  
let (unknownType : FStar_Extraction_ML_Syntax.mlty) =
  FStar_Extraction_ML_Syntax.MLTY_Top 
let (prependTick : Prims.string -> Prims.string) =
  fun x  -> if FStar_Util.starts_with x "'" then x else Prims.strcat "'A" x 
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
    let uu____334 = FStar_Extraction_ML_Syntax.bv_as_mlident x  in
    prependTick uu____334
  
let (bv_as_ml_termvar : FStar_Syntax_Syntax.bv -> Prims.string) =
  fun x  ->
    let uu____338 = FStar_Extraction_ML_Syntax.bv_as_mlident x  in
    removeTick uu____338
  
let rec (lookup_ty_local :
  binding Prims.list ->
    FStar_Syntax_Syntax.bv -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun gamma  ->
    fun b  ->
      match gamma with
      | (Bv (b',FStar_Util.Inl (mli,mlt)))::tl1 ->
          if FStar_Syntax_Syntax.bv_eq b b'
          then mlt
          else lookup_ty_local tl1 b
      | (Bv (b',FStar_Util.Inr uu____385))::tl1 ->
          if FStar_Syntax_Syntax.bv_eq b b'
          then
            failwith
              (Prims.strcat "Type/Expr clash: "
                 (b.FStar_Syntax_Syntax.ppname).FStar_Ident.idText)
          else lookup_ty_local tl1 b
      | uu____426::tl1 -> lookup_ty_local tl1 b
      | [] ->
          failwith
            (Prims.strcat "extraction: unbound type var "
               (b.FStar_Syntax_Syntax.ppname).FStar_Ident.idText)
  
let tyscheme_of_td :
  'Auu____435 'Auu____436 'Auu____437 'Auu____438 .
    ('Auu____435,'Auu____436,'Auu____437,FStar_Extraction_ML_Syntax.mlidents,
      'Auu____438,FStar_Extraction_ML_Syntax.mltybody
                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple6 ->
      FStar_Extraction_ML_Syntax.mltyscheme FStar_Pervasives_Native.option
  =
  fun uu____458  ->
    match uu____458 with
    | (uu____473,uu____474,uu____475,vars,uu____477,body_opt) ->
        (match body_opt with
         | FStar_Pervasives_Native.Some
             (FStar_Extraction_ML_Syntax.MLTD_Abbrev t) ->
             FStar_Pervasives_Native.Some (vars, t)
         | uu____492 -> FStar_Pervasives_Native.None)
  
let (lookup_ty_const :
  env ->
    FStar_Extraction_ML_Syntax.mlpath ->
      FStar_Extraction_ML_Syntax.mltyscheme FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun uu____502  ->
      match uu____502 with
      | (module_name,ty_name) ->
          FStar_Util.find_map env.tydefs
            (fun uu____525  ->
               match uu____525 with
               | (uu____536,m,tds) ->
                   if module_name = m
                   then
                     FStar_Util.find_map tds
                       (fun td  ->
                          let uu____556 = td  in
                          match uu____556 with
                          | (uu____559,n1,uu____561,uu____562,uu____563,uu____564)
                              ->
                              if n1 = ty_name
                              then tyscheme_of_td td
                              else FStar_Pervasives_Native.None)
                   else FStar_Pervasives_Native.None)
  
let (module_name_of_fv : FStar_Syntax_Syntax.fv -> Prims.string Prims.list) =
  fun fv  ->
    FStar_All.pipe_right
      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ns
      (FStar_List.map (fun i  -> i.FStar_Ident.idText))
  
let (maybe_mangle_type_projector :
  env ->
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
        (fun uu____622  ->
           match uu____622 with
           | (uu____639,m,tds) ->
               FStar_Util.find_map tds
                 (fun uu____659  ->
                    match uu____659 with
                    | (uu____668,n1,mangle_opt,uu____671,uu____672,uu____673)
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
  
let (lookup_tyvar :
  env -> FStar_Syntax_Syntax.bv -> FStar_Extraction_ML_Syntax.mlty) =
  fun g  -> fun bt  -> lookup_ty_local g.gamma bt 
let (lookup_fv_by_lid : env -> FStar_Ident.lident -> ty_or_exp_b) =
  fun g  ->
    fun lid  ->
      let x =
        FStar_Util.find_map g.gamma
          (fun uu___61_760  ->
             match uu___61_760 with
             | Fv (fv',x) when FStar_Syntax_Syntax.fv_eq_lid fv' lid ->
                 FStar_Pervasives_Native.Some x
             | uu____765 -> FStar_Pervasives_Native.None)
         in
      match x with
      | FStar_Pervasives_Native.None  ->
          let uu____766 =
            FStar_Util.format1 "free Variable %s not found\n"
              lid.FStar_Ident.nsstr
             in
          failwith uu____766
      | FStar_Pervasives_Native.Some y -> y
  
let (try_lookup_fv :
  env -> FStar_Syntax_Syntax.fv -> ty_or_exp_b FStar_Pervasives_Native.option)
  =
  fun g  ->
    fun fv  ->
      FStar_Util.find_map g.gamma
        (fun uu___62_781  ->
           match uu___62_781 with
           | Fv (fv',t) when FStar_Syntax_Syntax.fv_eq fv fv' ->
               FStar_Pervasives_Native.Some t
           | uu____786 -> FStar_Pervasives_Native.None)
  
let (lookup_fv : env -> FStar_Syntax_Syntax.fv -> ty_or_exp_b) =
  fun g  ->
    fun fv  ->
      let uu____793 = try_lookup_fv g fv  in
      match uu____793 with
      | FStar_Pervasives_Native.None  ->
          let uu____796 =
            let uu____797 =
              FStar_Range.string_of_range
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.p
               in
            let uu____798 =
              FStar_Syntax_Print.lid_to_string
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            FStar_Util.format2 "(%s) free Variable %s not found\n" uu____797
              uu____798
             in
          failwith uu____796
      | FStar_Pervasives_Native.Some y -> y
  
let (lookup_bv : env -> FStar_Syntax_Syntax.bv -> ty_or_exp_b) =
  fun g  ->
    fun bv  ->
      let x =
        FStar_Util.find_map g.gamma
          (fun uu___63_812  ->
             match uu___63_812 with
             | Bv (bv',r) when FStar_Syntax_Syntax.bv_eq bv bv' ->
                 FStar_Pervasives_Native.Some r
             | uu____817 -> FStar_Pervasives_Native.None)
         in
      match x with
      | FStar_Pervasives_Native.None  ->
          let uu____818 =
            let uu____819 =
              FStar_Range.string_of_range
                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange
               in
            let uu____820 = FStar_Syntax_Print.bv_to_string bv  in
            FStar_Util.format2 "(%s) bound Variable %s not found\n" uu____819
              uu____820
             in
          failwith uu____818
      | FStar_Pervasives_Native.Some y -> y
  
let (lookup :
  env ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
      (ty_or_exp_b,FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2)
  =
  fun g  ->
    fun x  ->
      match x with
      | FStar_Util.Inl x1 ->
          let uu____849 = lookup_bv g x1  in
          (uu____849, FStar_Pervasives_Native.None)
      | FStar_Util.Inr x1 ->
          let uu____853 = lookup_fv g x1  in
          (uu____853, (x1.FStar_Syntax_Syntax.fv_qual))
  
let (lookup_term :
  env ->
    FStar_Syntax_Syntax.term ->
      (ty_or_exp_b,FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2)
  =
  fun g  ->
    fun t  ->
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_name x -> lookup g (FStar_Util.Inl x)
      | FStar_Syntax_Syntax.Tm_fvar x -> lookup g (FStar_Util.Inr x)
      | uu____876 -> failwith "Impossible: lookup_term for a non-name"
  
let (extend_ty :
  env ->
    FStar_Syntax_Syntax.bv ->
      FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option -> env)
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
        let uu___65_931 = g  in
        {
          tcenv;
          gamma;
          tydefs = (uu___65_931.tydefs);
          type_names = (uu___65_931.type_names);
          currentModule = (uu___65_931.currentModule)
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
             let uu____957 =
               let uu____960 = valid c  in
               if uu____960 then [c] else [95; 95]  in
             FStar_List.append uu____957 cs1) cs []
       in
    let cs'1 =
      match cs' with
      | c::cs1 when (FStar_Util.is_digit c) || (c = 39) -> 95 :: c :: cs1
      | uu____983 -> cs  in
    FStar_String.string_of_list cs'1
  
let (find_uniq : binding Prims.list -> Prims.string -> Prims.string) =
  fun gamma  ->
    fun mlident  ->
      let rec find_uniq mlident1 i =
        let suffix =
          if i = (Prims.parse_int "0")
          then ""
          else FStar_Util.string_of_int i  in
        let target_mlident = Prims.strcat mlident1 suffix  in
        let has_collision =
          FStar_List.existsb
            (fun uu___64_1011  ->
               match uu___64_1011 with
               | Bv (uu____1012,FStar_Util.Inl (mlident',uu____1014)) ->
                   target_mlident = mlident'
               | Fv (uu____1043,FStar_Util.Inl (mlident',uu____1045)) ->
                   target_mlident = mlident'
               | Fv
                   (uu____1074,FStar_Util.Inr
                    (mlident',uu____1076,uu____1077,uu____1078))
                   -> target_mlident = mlident'
               | Bv
                   (uu____1107,FStar_Util.Inr
                    (mlident',uu____1109,uu____1110,uu____1111))
                   -> target_mlident = mlident') gamma
           in
        if has_collision
        then find_uniq mlident1 (i + (Prims.parse_int "1"))
        else target_mlident  in
      let mlident1 = sanitize mlident  in
      find_uniq mlident1 (Prims.parse_int "0")
  
let (extend_bv :
  env ->
    FStar_Syntax_Syntax.bv ->
      FStar_Extraction_ML_Syntax.mltyscheme ->
        Prims.bool ->
          Prims.bool ->
            Prims.bool ->
              (env,FStar_Extraction_ML_Syntax.mlident)
                FStar_Pervasives_Native.tuple2)
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
                | uu____1172 -> FStar_Extraction_ML_Syntax.MLTY_Top  in
              let mlident =
                let uu____1174 = FStar_Extraction_ML_Syntax.bv_as_mlident x
                   in
                find_uniq g.gamma uu____1174  in
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
                let uu____1215 = FStar_Syntax_Syntax.binders_of_list [x]  in
                FStar_TypeChecker_Env.push_binders g.tcenv uu____1215  in
              ((let uu___66_1217 = g  in
                {
                  tcenv;
                  gamma;
                  tydefs = (uu___66_1217.tydefs);
                  type_names = (uu___66_1217.type_names);
                  currentModule = (uu___66_1217.currentModule)
                }), mlident)
  
let rec (mltyFvars :
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlident Prims.list)
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Var x -> [x]
    | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,f,t2) ->
        let uu____1229 = mltyFvars t1  in
        let uu____1232 = mltyFvars t2  in
        FStar_List.append uu____1229 uu____1232
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
    let uu____1265 = mltyFvars (FStar_Pervasives_Native.snd tys)  in
    subsetMlidents uu____1265 (FStar_Pervasives_Native.fst tys)
  
let (extend_fv' :
  env ->
    FStar_Syntax_Syntax.fv ->
      FStar_Extraction_ML_Syntax.mlpath ->
        FStar_Extraction_ML_Syntax.mltyscheme ->
          Prims.bool ->
            Prims.bool ->
              (env,FStar_Extraction_ML_Syntax.mlident)
                FStar_Pervasives_Native.tuple2)
  =
  fun g  ->
    fun x  ->
      fun y  ->
        fun t_x  ->
          fun add_unit  ->
            fun is_rec  ->
              let uu____1294 = tySchemeIsClosed t_x  in
              if uu____1294
              then
                let ml_ty =
                  match t_x with
                  | ([],t) -> t
                  | uu____1303 -> FStar_Extraction_ML_Syntax.MLTY_Top  in
                let uu____1304 =
                  let uu____1315 = y  in
                  match uu____1315 with
                  | (ns,i) ->
                      let mlsymbol =
                        FStar_Extraction_ML_Syntax.avoid_keyword i  in
                      ((ns, mlsymbol), mlsymbol)
                   in
                match uu____1304 with
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
                    ((let uu___67_1398 = g  in
                      {
                        tcenv = (uu___67_1398.tcenv);
                        gamma;
                        tydefs = (uu___67_1398.tydefs);
                        type_names = (uu___67_1398.type_names);
                        currentModule = (uu___67_1398.currentModule)
                      }), mlsymbol)
              else failwith "freevars found"
  
let (extend_fv :
  env ->
    FStar_Syntax_Syntax.fv ->
      FStar_Extraction_ML_Syntax.mltyscheme ->
        Prims.bool ->
          Prims.bool ->
            (env,FStar_Extraction_ML_Syntax.mlident)
              FStar_Pervasives_Native.tuple2)
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
  env ->
    FStar_Syntax_Syntax.lbname ->
      FStar_Syntax_Syntax.typ ->
        FStar_Extraction_ML_Syntax.mltyscheme ->
          Prims.bool ->
            Prims.bool ->
              (env,FStar_Extraction_ML_Syntax.mlident)
                FStar_Pervasives_Native.tuple2)
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
                  let uu____1456 =
                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                      (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                     in
                  (match uu____1456 with
                   | (p,y) -> extend_fv' g f (p, y) t_x add_unit is_rec)
  
let (extend_tydef :
  env -> FStar_Syntax_Syntax.fv -> FStar_Extraction_ML_Syntax.mltydecl -> env)
  =
  fun g  ->
    fun fv  ->
      fun td  ->
        let m = module_name_of_fv fv  in
        let uu___68_1481 = g  in
        {
          tcenv = (uu___68_1481.tcenv);
          gamma = (uu___68_1481.gamma);
          tydefs = ((fv, m, td) :: (g.tydefs));
          type_names = (fv :: (g.type_names));
          currentModule = (uu___68_1481.currentModule)
        }
  
let (extend_type_name : env -> FStar_Syntax_Syntax.fv -> env) =
  fun g  ->
    fun fv  ->
      let uu___69_1498 = g  in
      {
        tcenv = (uu___69_1498.tcenv);
        gamma = (uu___69_1498.gamma);
        tydefs = (uu___69_1498.tydefs);
        type_names = (fv :: (g.type_names));
        currentModule = (uu___69_1498.currentModule)
      }
  
let (is_type_name : env -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun g  ->
    fun fv  ->
      FStar_All.pipe_right g.type_names
        (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq fv))
  
let (is_fv_type : env -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun g  ->
    fun fv  ->
      (is_type_name g fv) ||
        (FStar_All.pipe_right g.tydefs
           (FStar_Util.for_some
              (fun uu____1535  ->
                 match uu____1535 with
                 | (fv',uu____1545,uu____1546) ->
                     FStar_Syntax_Syntax.fv_eq fv fv')))
  
let (emptyMlPath :
  (FStar_Extraction_ML_Syntax.mlsymbol Prims.list,Prims.string)
    FStar_Pervasives_Native.tuple2)
  = ([], "") 
let (mkContext : FStar_TypeChecker_Env.env -> env) =
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
    let uu____1591 =
      let uu____1596 =
        let uu____1597 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.failwith_lid
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None
           in
        FStar_Util.Inr uu____1597  in
      extend_lb env uu____1596 FStar_Syntax_Syntax.tun failwith_ty false
        false
       in
    FStar_All.pipe_right uu____1591 FStar_Pervasives_Native.fst
  
let (monad_op_name :
  FStar_Syntax_Syntax.eff_decl ->
    Prims.string ->
      (FStar_Extraction_ML_Syntax.mlpath,FStar_Ident.lident)
        FStar_Pervasives_Native.tuple2)
  =
  fun ed  ->
    fun nm  ->
      let lid =
        let uu____1613 = FStar_Ident.id_of_text nm  in
        FStar_Syntax_Util.mk_field_projector_name_from_ident
          ed.FStar_Syntax_Syntax.mname uu____1613
         in
      let uu____1614 = FStar_Extraction_ML_Syntax.mlpath_of_lident lid  in
      (uu____1614, lid)
  
let (action_name :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.action ->
      (FStar_Extraction_ML_Syntax.mlpath,FStar_Ident.lident)
        FStar_Pervasives_Native.tuple2)
  =
  fun ed  ->
    fun a  ->
      let nm =
        ((a.FStar_Syntax_Syntax.action_name).FStar_Ident.ident).FStar_Ident.idText
         in
      let module_name = (ed.FStar_Syntax_Syntax.mname).FStar_Ident.ns  in
      let lid =
        let uu____1630 =
          let uu____1633 =
            let uu____1636 = FStar_Ident.id_of_text nm  in [uu____1636]  in
          FStar_List.append module_name uu____1633  in
        FStar_Ident.lid_of_ids uu____1630  in
      let uu____1637 = FStar_Extraction_ML_Syntax.mlpath_of_lident lid  in
      (uu____1637, lid)
  
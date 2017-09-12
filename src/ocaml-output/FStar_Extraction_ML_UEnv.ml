open Prims
type ty_or_exp_b =
  ((FStar_Extraction_ML_Syntax.mlident,FStar_Extraction_ML_Syntax.mlty)
     FStar_Pervasives_Native.tuple2,(FStar_Extraction_ML_Syntax.mlsymbol,
                                      FStar_Extraction_ML_Syntax.mlexpr,
                                      FStar_Extraction_ML_Syntax.mltyscheme,
                                      Prims.bool)
                                      FStar_Pervasives_Native.tuple4)
    FStar_Util.either
type binding =
  | Bv of (FStar_Syntax_Syntax.bv,ty_or_exp_b)
  FStar_Pervasives_Native.tuple2
  | Fv of (FStar_Syntax_Syntax.fv,ty_or_exp_b) FStar_Pervasives_Native.tuple2
let uu___is_Bv: binding -> Prims.bool =
  fun projectee  -> match projectee with | Bv _0 -> true | uu____42 -> false
let __proj__Bv__item___0:
  binding ->
    (FStar_Syntax_Syntax.bv,ty_or_exp_b) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Bv _0 -> _0
let uu___is_Fv: binding -> Prims.bool =
  fun projectee  -> match projectee with | Fv _0 -> true | uu____72 -> false
let __proj__Fv__item___0:
  binding ->
    (FStar_Syntax_Syntax.fv,ty_or_exp_b) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Fv _0 -> _0
type env =
  {
  tcenv: FStar_TypeChecker_Env.env;
  gamma: binding Prims.list;
  tydefs:
    (FStar_Extraction_ML_Syntax.mlsymbol Prims.list,FStar_Extraction_ML_Syntax.mltydecl)
      FStar_Pervasives_Native.tuple2 Prims.list;
  type_names: FStar_Syntax_Syntax.fv Prims.list;
  currentModule: FStar_Extraction_ML_Syntax.mlpath;}
let __proj__Mkenv__item__tcenv: env -> FStar_TypeChecker_Env.env =
  fun projectee  ->
    match projectee with
    | { tcenv = __fname__tcenv; gamma = __fname__gamma;
        tydefs = __fname__tydefs; type_names = __fname__type_names;
        currentModule = __fname__currentModule;_} -> __fname__tcenv
let __proj__Mkenv__item__gamma: env -> binding Prims.list =
  fun projectee  ->
    match projectee with
    | { tcenv = __fname__tcenv; gamma = __fname__gamma;
        tydefs = __fname__tydefs; type_names = __fname__type_names;
        currentModule = __fname__currentModule;_} -> __fname__gamma
let __proj__Mkenv__item__tydefs:
  env ->
    (FStar_Extraction_ML_Syntax.mlsymbol Prims.list,FStar_Extraction_ML_Syntax.mltydecl)
      FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun projectee  ->
    match projectee with
    | { tcenv = __fname__tcenv; gamma = __fname__gamma;
        tydefs = __fname__tydefs; type_names = __fname__type_names;
        currentModule = __fname__currentModule;_} -> __fname__tydefs
let __proj__Mkenv__item__type_names: env -> FStar_Syntax_Syntax.fv Prims.list
  =
  fun projectee  ->
    match projectee with
    | { tcenv = __fname__tcenv; gamma = __fname__gamma;
        tydefs = __fname__tydefs; type_names = __fname__type_names;
        currentModule = __fname__currentModule;_} -> __fname__type_names
let __proj__Mkenv__item__currentModule:
  env -> FStar_Extraction_ML_Syntax.mlpath =
  fun projectee  ->
    match projectee with
    | { tcenv = __fname__tcenv; gamma = __fname__gamma;
        tydefs = __fname__tydefs; type_names = __fname__type_names;
        currentModule = __fname__currentModule;_} -> __fname__currentModule
let debug: env -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun g  ->
    fun f  ->
      let c = FStar_Extraction_ML_Syntax.string_of_mlpath g.currentModule in
      let uu____268 =
        FStar_Options.debug_at_level c (FStar_Options.Other "Extraction") in
      if uu____268 then f () else ()
let mkFvvar:
  FStar_Ident.lident -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.fv =
  fun l  ->
    fun t  ->
      FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant
        FStar_Pervasives_Native.None
let erasedContent: FStar_Extraction_ML_Syntax.mlty =
  FStar_Extraction_ML_Syntax.ml_unit_ty
let erasableTypeNoDelta: FStar_Extraction_ML_Syntax.mlty -> Prims.bool =
  fun t  ->
    if t = FStar_Extraction_ML_Syntax.ml_unit_ty
    then true
    else
      (match t with
       | FStar_Extraction_ML_Syntax.MLTY_Named
           (uu____283,("FStar"::"Ghost"::[],"erased")) -> true
       | uu____296 -> false)
let unknownType: FStar_Extraction_ML_Syntax.mlty =
  FStar_Extraction_ML_Syntax.MLTY_Top
let prependTick:
  'Auu____301 .
    (Prims.string,'Auu____301) FStar_Pervasives_Native.tuple2 ->
      (Prims.string,'Auu____301) FStar_Pervasives_Native.tuple2
  =
  fun uu____313  ->
    match uu____313 with
    | (x,n1) ->
        if FStar_Util.starts_with x "'"
        then (x, n1)
        else ((Prims.strcat "'A" x), n1)
let removeTick:
  'Auu____329 .
    (Prims.string,'Auu____329) FStar_Pervasives_Native.tuple2 ->
      (Prims.string,'Auu____329) FStar_Pervasives_Native.tuple2
  =
  fun uu____341  ->
    match uu____341 with
    | (x,n1) ->
        if FStar_Util.starts_with x "'"
        then
          let uu____352 = FStar_Util.substring_from x (Prims.parse_int "1") in
          (uu____352, n1)
        else (x, n1)
let convRange: FStar_Range.range -> Prims.int = fun r  -> Prims.parse_int "0"
let convIdent: FStar_Ident.ident -> FStar_Extraction_ML_Syntax.mlident =
  fun id  -> ((id.FStar_Ident.idText), (Prims.parse_int "0"))
let bv_as_ml_tyvar:
  FStar_Syntax_Syntax.bv ->
    (Prims.string,Prims.int) FStar_Pervasives_Native.tuple2
  =
  fun x  ->
    let uu____370 = FStar_Extraction_ML_Syntax.bv_as_mlident x in
    prependTick uu____370
let bv_as_ml_termvar:
  FStar_Syntax_Syntax.bv ->
    (Prims.string,Prims.int) FStar_Pervasives_Native.tuple2
  =
  fun x  ->
    let uu____383 = FStar_Extraction_ML_Syntax.bv_as_mlident x in
    removeTick uu____383
let rec lookup_ty_local:
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
      | (Bv (b',FStar_Util.Inr uu____436))::tl1 ->
          if FStar_Syntax_Syntax.bv_eq b b'
          then
            failwith
              (Prims.strcat "Type/Expr clash: "
                 (b.FStar_Syntax_Syntax.ppname).FStar_Ident.idText)
          else lookup_ty_local tl1 b
      | uu____477::tl1 -> lookup_ty_local tl1 b
      | [] ->
          failwith
            (Prims.strcat "extraction: unbound type var "
               (b.FStar_Syntax_Syntax.ppname).FStar_Ident.idText)
let tyscheme_of_td:
  'Auu____491 'Auu____492 'Auu____493 'Auu____494 .
    ('Auu____494,'Auu____493,'Auu____492,FStar_Extraction_ML_Syntax.mlidents,
      'Auu____491,FStar_Extraction_ML_Syntax.mltybody
                    FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple6 ->
      FStar_Extraction_ML_Syntax.mltyscheme FStar_Pervasives_Native.option
  =
  fun uu____514  ->
    match uu____514 with
    | (uu____529,uu____530,uu____531,vars,uu____533,body_opt) ->
        (match body_opt with
         | FStar_Pervasives_Native.Some
             (FStar_Extraction_ML_Syntax.MLTD_Abbrev t) ->
             FStar_Pervasives_Native.Some (vars, t)
         | uu____548 -> FStar_Pervasives_Native.None)
let lookup_ty_const:
  env ->
    FStar_Extraction_ML_Syntax.mlpath ->
      FStar_Extraction_ML_Syntax.mltyscheme FStar_Pervasives_Native.option
  =
  fun env  ->
    fun uu____560  ->
      match uu____560 with
      | (module_name,ty_name) ->
          FStar_Util.find_map env.tydefs
            (fun uu____580  ->
               match uu____580 with
               | (m,tds) ->
                   if module_name = m
                   then
                     FStar_Util.find_map tds
                       (fun td  ->
                          let uu____608 = td in
                          match uu____608 with
                          | (uu____611,n1,uu____613,uu____614,uu____615,uu____616)
                              ->
                              if n1 = ty_name
                              then tyscheme_of_td td
                              else FStar_Pervasives_Native.None)
                   else FStar_Pervasives_Native.None)
let module_name_of_fv: FStar_Syntax_Syntax.fv -> Prims.string Prims.list =
  fun fv  ->
    FStar_All.pipe_right
      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ns
      (FStar_List.map (fun i  -> i.FStar_Ident.idText))
let maybe_mangle_type_projector:
  env ->
    FStar_Syntax_Syntax.fv ->
      FStar_Extraction_ML_Syntax.mlpath FStar_Pervasives_Native.option
  =
  fun env  ->
    fun fv  ->
      let mname = module_name_of_fv fv in
      let ty_name =
        (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText in
      FStar_Util.find_map env.tydefs
        (fun uu____674  ->
           match uu____674 with
           | (m,tds) ->
               FStar_Util.find_map tds
                 (fun uu____708  ->
                    match uu____708 with
                    | (uu____717,n1,mangle_opt,uu____720,uu____721,uu____722)
                        ->
                        if m = mname
                        then
                          (if n1 = ty_name
                           then
                             match mangle_opt with
                             | FStar_Pervasives_Native.None  ->
                                 FStar_Pervasives_Native.Some (m, n1)
                             | FStar_Pervasives_Native.Some mangled ->
                                 let modul = m in
                                 FStar_Pervasives_Native.Some
                                   (modul, mangled)
                           else FStar_Pervasives_Native.None)
                        else FStar_Pervasives_Native.None))
let lookup_tyvar:
  env -> FStar_Syntax_Syntax.bv -> FStar_Extraction_ML_Syntax.mlty =
  fun g  -> fun bt  -> lookup_ty_local g.gamma bt
let lookup_fv_by_lid: env -> FStar_Ident.lident -> ty_or_exp_b =
  fun g  ->
    fun lid  ->
      let x =
        FStar_Util.find_map g.gamma
          (fun uu___108_813  ->
             match uu___108_813 with
             | Fv (fv',x) when FStar_Syntax_Syntax.fv_eq_lid fv' lid ->
                 FStar_Pervasives_Native.Some x
             | uu____818 -> FStar_Pervasives_Native.None) in
      match x with
      | FStar_Pervasives_Native.None  ->
          let uu____819 =
            FStar_Util.format1 "free Variable %s not found\n"
              lid.FStar_Ident.nsstr in
          failwith uu____819
      | FStar_Pervasives_Native.Some y -> y
let lookup_fv: env -> FStar_Syntax_Syntax.fv -> ty_or_exp_b =
  fun g  ->
    fun fv  ->
      let x =
        FStar_Util.find_map g.gamma
          (fun uu___109_835  ->
             match uu___109_835 with
             | Fv (fv',t) when FStar_Syntax_Syntax.fv_eq fv fv' ->
                 FStar_Pervasives_Native.Some t
             | uu____840 -> FStar_Pervasives_Native.None) in
      match x with
      | FStar_Pervasives_Native.None  ->
          let uu____841 =
            let uu____842 =
              FStar_Range.string_of_range
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.p in
            let uu____843 =
              FStar_Syntax_Print.lid_to_string
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            FStar_Util.format2 "(%s) free Variable %s not found\n" uu____842
              uu____843 in
          failwith uu____841
      | FStar_Pervasives_Native.Some y -> y
let lookup_bv: env -> FStar_Syntax_Syntax.bv -> ty_or_exp_b =
  fun g  ->
    fun bv  ->
      let x =
        FStar_Util.find_map g.gamma
          (fun uu___110_859  ->
             match uu___110_859 with
             | Bv (bv',r) when FStar_Syntax_Syntax.bv_eq bv bv' ->
                 FStar_Pervasives_Native.Some r
             | uu____864 -> FStar_Pervasives_Native.None) in
      match x with
      | FStar_Pervasives_Native.None  ->
          let uu____865 =
            let uu____866 =
              FStar_Range.string_of_range
                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange in
            let uu____867 = FStar_Syntax_Print.bv_to_string bv in
            FStar_Util.format2 "(%s) bound Variable %s not found\n" uu____866
              uu____867 in
          failwith uu____865
      | FStar_Pervasives_Native.Some y -> y
let lookup:
  env ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
      (ty_or_exp_b,FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2
  =
  fun g  ->
    fun x  ->
      match x with
      | FStar_Util.Inl x1 ->
          let uu____898 = lookup_bv g x1 in
          (uu____898, FStar_Pervasives_Native.None)
      | FStar_Util.Inr x1 ->
          let uu____902 = lookup_fv g x1 in
          (uu____902, (x1.FStar_Syntax_Syntax.fv_qual))
let lookup_term:
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
      | uu____927 -> failwith "Impossible: lookup_term for a non-name"
let extend_ty:
  env ->
    FStar_Syntax_Syntax.bv ->
      FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option -> env
  =
  fun g  ->
    fun a  ->
      fun mapped_to  ->
        let ml_a = bv_as_ml_tyvar a in
        let mapped_to1 =
          match mapped_to with
          | FStar_Pervasives_Native.None  ->
              FStar_Extraction_ML_Syntax.MLTY_Var ml_a
          | FStar_Pervasives_Native.Some t -> t in
        let gamma = (Bv (a, (FStar_Util.Inl (ml_a, mapped_to1)))) ::
          (g.gamma) in
        let tcenv = FStar_TypeChecker_Env.push_bv g.tcenv a in
        let uu___112_1001 = g in
        {
          tcenv;
          gamma;
          tydefs = (uu___112_1001.tydefs);
          type_names = (uu___112_1001.type_names);
          currentModule = (uu___112_1001.currentModule)
        }
let sanitize: Prims.string -> Prims.string =
  fun s  ->
    let cs = FStar_String.list_of_string s in
    let valid c = ((FStar_Util.is_letter_or_digit c) || (c = 95)) || (c = 39) in
    let cs' =
      FStar_List.fold_right
        (fun c  ->
           fun cs1  ->
             let uu____1025 =
               let uu____1028 = valid c in
               if uu____1028 then [c] else [95; 95] in
             FStar_List.append uu____1025 cs1) cs [] in
    let cs'1 =
      match cs' with
      | c::cs1 when (FStar_Util.is_digit c) || (c = 39) -> 95 :: c :: cs1
      | uu____1041 -> cs in
    FStar_String.string_of_list cs'1
let find_uniq: binding Prims.list -> Prims.string -> Prims.string =
  fun gamma  ->
    fun mlident  ->
      let rec find_uniq mlident1 i =
        let suffix =
          if i = (Prims.parse_int "0")
          then ""
          else FStar_Util.string_of_int i in
        let target_mlident = Prims.strcat mlident1 suffix in
        let has_collision =
          FStar_List.existsb
            (fun uu___111_1071  ->
               match uu___111_1071 with
               | Bv (uu____1072,FStar_Util.Inl (mlident',uu____1074)) ->
                   target_mlident = (FStar_Pervasives_Native.fst mlident')
               | Fv (uu____1103,FStar_Util.Inl (mlident',uu____1105)) ->
                   target_mlident = (FStar_Pervasives_Native.fst mlident')
               | Fv
                   (uu____1134,FStar_Util.Inr
                    (mlident',uu____1136,uu____1137,uu____1138))
                   -> target_mlident = mlident'
               | Bv
                   (uu____1167,FStar_Util.Inr
                    (mlident',uu____1169,uu____1170,uu____1171))
                   -> target_mlident = mlident') gamma in
        if has_collision
        then find_uniq mlident1 (i + (Prims.parse_int "1"))
        else target_mlident in
      let mlident1 = sanitize mlident in
      find_uniq mlident1 (Prims.parse_int "0")
let extend_bv:
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
                | uu____1238 -> FStar_Extraction_ML_Syntax.MLTY_Top in
              let uu____1239 = FStar_Extraction_ML_Syntax.bv_as_mlident x in
              match uu____1239 with
              | (mlident,nocluewhat) ->
                  let mlsymbol = find_uniq g.gamma mlident in
                  let mlident1 = (mlsymbol, nocluewhat) in
                  let mlx = FStar_Extraction_ML_Syntax.MLE_Var mlident1 in
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
                  let gamma =
                    (Bv (x, (FStar_Util.Inr (mlsymbol, mlx1, t_x1, is_rec))))
                    :: (g.gamma) in
                  let tcenv =
                    let uu____1292 = FStar_Syntax_Syntax.binders_of_list [x] in
                    FStar_TypeChecker_Env.push_binders g.tcenv uu____1292 in
                  ((let uu___113_1298 = g in
                    {
                      tcenv;
                      gamma;
                      tydefs = (uu___113_1298.tydefs);
                      type_names = (uu___113_1298.type_names);
                      currentModule = (uu___113_1298.currentModule)
                    }), mlident1)
let rec mltyFvars:
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlident Prims.list
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Var x -> [x]
    | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,f,t2) ->
        let uu____1311 = mltyFvars t1 in
        let uu____1314 = mltyFvars t2 in
        FStar_List.append uu____1311 uu____1314
    | FStar_Extraction_ML_Syntax.MLTY_Named (args,path) ->
        FStar_List.collect mltyFvars args
    | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
        FStar_List.collect mltyFvars ts
    | FStar_Extraction_ML_Syntax.MLTY_Top  -> []
let rec subsetMlidents:
  FStar_Extraction_ML_Syntax.mlident Prims.list ->
    FStar_Extraction_ML_Syntax.mlident Prims.list -> Prims.bool
  =
  fun la  ->
    fun lb  ->
      match la with
      | h::tla -> (FStar_List.contains h lb) && (subsetMlidents tla lb)
      | [] -> true
let tySchemeIsClosed: FStar_Extraction_ML_Syntax.mltyscheme -> Prims.bool =
  fun tys  ->
    let uu____1350 = mltyFvars (FStar_Pervasives_Native.snd tys) in
    subsetMlidents uu____1350 (FStar_Pervasives_Native.fst tys)
let extend_fv':
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
              let uu____1385 = tySchemeIsClosed t_x in
              if uu____1385
              then
                let ml_ty =
                  match t_x with
                  | ([],t) -> t
                  | uu____1394 -> FStar_Extraction_ML_Syntax.MLTY_Top in
                let uu____1395 =
                  let uu____1406 = y in
                  match uu____1406 with
                  | (ns,i) ->
                      let mlsymbol =
                        FStar_Extraction_ML_Syntax.avoid_keyword i in
                      ((ns, mlsymbol), mlsymbol) in
                match uu____1395 with
                | (mlpath,mlsymbol) ->
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
                    let gamma =
                      (Fv
                         (x, (FStar_Util.Inr (mlsymbol, mly1, t_x1, is_rec))))
                      :: (g.gamma) in
                    ((let uu___114_1493 = g in
                      {
                        tcenv = (uu___114_1493.tcenv);
                        gamma;
                        tydefs = (uu___114_1493.tydefs);
                        type_names = (uu___114_1493.type_names);
                        currentModule = (uu___114_1493.currentModule)
                      }), (mlsymbol, (Prims.parse_int "0")))
              else failwith "freevars found"
let extend_fv:
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
                (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            extend_fv' g x mlp t_x add_unit is_rec
let extend_lb:
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
                  let uu____1562 =
                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                      (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  (match uu____1562 with
                   | (p,y) -> extend_fv' g f (p, y) t_x add_unit is_rec)
let extend_tydef:
  env -> FStar_Syntax_Syntax.fv -> FStar_Extraction_ML_Syntax.mltydecl -> env
  =
  fun g  ->
    fun fv  ->
      fun td  ->
        let m = module_name_of_fv fv in
        let uu___115_1590 = g in
        {
          tcenv = (uu___115_1590.tcenv);
          gamma = (uu___115_1590.gamma);
          tydefs = ((m, td) :: (g.tydefs));
          type_names = (fv :: (g.type_names));
          currentModule = (uu___115_1590.currentModule)
        }
let extend_type_name: env -> FStar_Syntax_Syntax.fv -> env =
  fun g  ->
    fun fv  ->
      let uu___116_1607 = g in
      {
        tcenv = (uu___116_1607.tcenv);
        gamma = (uu___116_1607.gamma);
        tydefs = (uu___116_1607.tydefs);
        type_names = (fv :: (g.type_names));
        currentModule = (uu___116_1607.currentModule)
      }
let is_type_name: env -> FStar_Syntax_Syntax.fv -> Prims.bool =
  fun g  ->
    fun fv  ->
      FStar_All.pipe_right g.type_names
        (FStar_Util.for_some (FStar_Syntax_Syntax.fv_eq fv))
let emptyMlPath:
  (FStar_Extraction_ML_Syntax.mlsymbol Prims.list,Prims.string)
    FStar_Pervasives_Native.tuple2
  = ([], "")
let mkContext: FStar_TypeChecker_Env.env -> env =
  fun e  ->
    let env =
      {
        tcenv = e;
        gamma = [];
        tydefs = [];
        type_names = [];
        currentModule = emptyMlPath
      } in
    let a = ("'a", (- (Prims.parse_int "1"))) in
    let failwith_ty =
      ([a],
        (FStar_Extraction_ML_Syntax.MLTY_Fun
           ((FStar_Extraction_ML_Syntax.MLTY_Named
               ([], (["Prims"], "string"))),
             FStar_Extraction_ML_Syntax.E_IMPURE,
             (FStar_Extraction_ML_Syntax.MLTY_Var a)))) in
    let uu____1677 =
      let uu____1682 =
        let uu____1683 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Parser_Const.failwith_lid
            FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None in
        FStar_Util.Inr uu____1683 in
      extend_lb env uu____1682 FStar_Syntax_Syntax.tun failwith_ty false
        false in
    FStar_All.pipe_right uu____1677 FStar_Pervasives_Native.fst
let monad_op_name:
  FStar_Syntax_Syntax.eff_decl ->
    Prims.string ->
      (FStar_Extraction_ML_Syntax.mlpath,FStar_Ident.lident)
        FStar_Pervasives_Native.tuple2
  =
  fun ed  ->
    fun nm  ->
      let lid =
        FStar_Syntax_Util.mk_field_projector_name_from_ident
          ed.FStar_Syntax_Syntax.mname (FStar_Ident.id_of_text nm) in
      let uu____1701 = FStar_Extraction_ML_Syntax.mlpath_of_lident lid in
      (uu____1701, lid)
let action_name:
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.action ->
      (FStar_Extraction_ML_Syntax.mlpath,FStar_Ident.lident)
        FStar_Pervasives_Native.tuple2
  =
  fun ed  ->
    fun a  ->
      let nm =
        ((a.FStar_Syntax_Syntax.action_name).FStar_Ident.ident).FStar_Ident.idText in
      let module_name = (ed.FStar_Syntax_Syntax.mname).FStar_Ident.ns in
      let lid =
        FStar_Ident.lid_of_ids
          (FStar_List.append module_name [FStar_Ident.id_of_text nm]) in
      let uu____1719 = FStar_Extraction_ML_Syntax.mlpath_of_lident lid in
      (uu____1719, lid)
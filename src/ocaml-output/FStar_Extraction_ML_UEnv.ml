open Prims
type ty_or_exp_b =
  ((FStar_Extraction_ML_Syntax.mlident* FStar_Extraction_ML_Syntax.mlty),
    (FStar_Extraction_ML_Syntax.mlsymbol* FStar_Extraction_ML_Syntax.mlexpr*
      FStar_Extraction_ML_Syntax.mltyscheme* Prims.bool))
    FStar_Util.either
type binding =
  | Bv of (FStar_Syntax_Syntax.bv* ty_or_exp_b)
  | Fv of (FStar_Syntax_Syntax.fv* ty_or_exp_b)
let uu___is_Bv: binding -> Prims.bool =
  fun projectee  -> match projectee with | Bv _0 -> true | uu____28 -> false
let __proj__Bv__item___0: binding -> (FStar_Syntax_Syntax.bv* ty_or_exp_b) =
  fun projectee  -> match projectee with | Bv _0 -> _0
let uu___is_Fv: binding -> Prims.bool =
  fun projectee  -> match projectee with | Fv _0 -> true | uu____50 -> false
let __proj__Fv__item___0: binding -> (FStar_Syntax_Syntax.fv* ty_or_exp_b) =
  fun projectee  -> match projectee with | Fv _0 -> _0
type env =
  {
  tcenv: FStar_TypeChecker_Env.env;
  gamma: binding Prims.list;
  tydefs:
    (FStar_Extraction_ML_Syntax.mlsymbol Prims.list*
      FStar_Extraction_ML_Syntax.mltydecl) Prims.list;
  currentModule: FStar_Extraction_ML_Syntax.mlpath;}
let __proj__Mkenv__item__tcenv: env -> FStar_TypeChecker_Env.env =
  fun projectee  ->
    match projectee with
    | { tcenv = __fname__tcenv; gamma = __fname__gamma;
        tydefs = __fname__tydefs; currentModule = __fname__currentModule;_}
        -> __fname__tcenv
let __proj__Mkenv__item__gamma: env -> binding Prims.list =
  fun projectee  ->
    match projectee with
    | { tcenv = __fname__tcenv; gamma = __fname__gamma;
        tydefs = __fname__tydefs; currentModule = __fname__currentModule;_}
        -> __fname__gamma
let __proj__Mkenv__item__tydefs:
  env ->
    (FStar_Extraction_ML_Syntax.mlsymbol Prims.list*
      FStar_Extraction_ML_Syntax.mltydecl) Prims.list
  =
  fun projectee  ->
    match projectee with
    | { tcenv = __fname__tcenv; gamma = __fname__gamma;
        tydefs = __fname__tydefs; currentModule = __fname__currentModule;_}
        -> __fname__tydefs
let __proj__Mkenv__item__currentModule:
  env -> FStar_Extraction_ML_Syntax.mlpath =
  fun projectee  ->
    match projectee with
    | { tcenv = __fname__tcenv; gamma = __fname__gamma;
        tydefs = __fname__tydefs; currentModule = __fname__currentModule;_}
        -> __fname__currentModule
let debug: env -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun g  ->
    fun f  ->
      let c = FStar_Extraction_ML_Syntax.string_of_mlpath g.currentModule in
      let uu____162 =
        FStar_Options.debug_at_level c (FStar_Options.Other "Extraction") in
      if uu____162 then f () else ()
let mkFvvar:
  FStar_Ident.lident -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.fv =
  fun l  ->
    fun t  ->
      FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant None
let erasedContent: FStar_Extraction_ML_Syntax.mlty =
  FStar_Extraction_ML_Syntax.ml_unit_ty
let erasableTypeNoDelta: FStar_Extraction_ML_Syntax.mlty -> Prims.bool =
  fun t  ->
    if t = FStar_Extraction_ML_Syntax.ml_unit_ty
    then true
    else
      (match t with
       | FStar_Extraction_ML_Syntax.MLTY_Named
           (uu____177,("FStar"::"Ghost"::[],"erased")) -> true
       | uu____184 -> false)
let unknownType: FStar_Extraction_ML_Syntax.mlty =
  FStar_Extraction_ML_Syntax.MLTY_Top
let prependTick uu____197 =
  match uu____197 with
  | (x,n1) ->
      if FStar_Util.starts_with x "'"
      then (x, n1)
      else ((Prims.strcat "'A" x), n1)
let removeTick uu____217 =
  match uu____217 with
  | (x,n1) ->
      if FStar_Util.starts_with x "'"
      then
        let uu____224 = FStar_Util.substring_from x (Prims.parse_int "1") in
        (uu____224, n1)
      else (x, n1)
let convRange: FStar_Range.range -> Prims.int = fun r  -> Prims.parse_int "0"
let convIdent: FStar_Ident.ident -> (Prims.string* Prims.int) =
  fun id  -> ((id.FStar_Ident.idText), (Prims.parse_int "0"))
let bv_as_ml_tyvar: FStar_Syntax_Syntax.bv -> (Prims.string* Prims.int) =
  fun x  ->
    let uu____240 = FStar_Extraction_ML_Syntax.bv_as_mlident x in
    prependTick uu____240
let bv_as_ml_termvar: FStar_Syntax_Syntax.bv -> (Prims.string* Prims.int) =
  fun x  ->
    let uu____249 = FStar_Extraction_ML_Syntax.bv_as_mlident x in
    removeTick uu____249
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
      | (Bv (b',FStar_Util.Inr uu____283))::tl1 ->
          if FStar_Syntax_Syntax.bv_eq b b'
          then
            failwith
              (Prims.strcat "Type/Expr clash: "
                 (b.FStar_Syntax_Syntax.ppname).FStar_Ident.idText)
          else lookup_ty_local tl1 b
      | uu____305::tl1 -> lookup_ty_local tl1 b
      | [] ->
          failwith
            (Prims.strcat "extraction: unbound type var "
               (b.FStar_Syntax_Syntax.ppname).FStar_Ident.idText)
let tyscheme_of_td uu____329 =
  match uu____329 with
  | (uu____336,uu____337,uu____338,vars,body_opt) ->
      (match body_opt with
       | Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev t) -> Some (vars, t)
       | uu____348 -> None)
let lookup_ty_const:
  env ->
    FStar_Extraction_ML_Syntax.mlpath ->
      FStar_Extraction_ML_Syntax.mltyscheme option
  =
  fun env  ->
    fun uu____358  ->
      match uu____358 with
      | (module_name,ty_name) ->
          FStar_Util.find_map env.tydefs
<<<<<<< HEAD
            (fun uu____310  ->
               match uu____310 with
=======
            (fun uu____368  ->
               match uu____368 with
>>>>>>> origin/guido_tactics
               | (m,tds) ->
                   if module_name = m
                   then
                     FStar_Util.find_map tds
                       (fun td  ->
<<<<<<< HEAD
                          let uu____329 = td in
                          match uu____329 with
                          | (uu____331,n1,uu____333,uu____334,uu____335) ->
=======
                          let uu____380 = td in
                          match uu____380 with
                          | (uu____382,n1,uu____384,uu____385,uu____386) ->
>>>>>>> origin/guido_tactics
                              if n1 = ty_name
                              then tyscheme_of_td td
                              else None)
                   else None)
let module_name_of_fv: FStar_Syntax_Syntax.fv -> Prims.string Prims.list =
  fun fv  ->
    FStar_All.pipe_right
      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ns
      (FStar_List.map (fun i  -> i.FStar_Ident.idText))
let maybe_mangle_type_projector:
  env ->
    FStar_Syntax_Syntax.fv ->
      (FStar_Extraction_ML_Syntax.mlsymbol Prims.list*
        FStar_Extraction_ML_Syntax.mlsymbol) option
  =
  fun env  ->
    fun fv  ->
      let mname = module_name_of_fv fv in
      let ty_name =
        (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText in
      FStar_Util.find_map env.tydefs
<<<<<<< HEAD
        (fun uu____372  ->
           match uu____372 with
           | (m,tds) ->
               FStar_Util.find_map tds
                 (fun uu____393  ->
                    match uu____393 with
                    | (uu____398,n1,mangle_opt,uu____401,uu____402) ->
=======
        (fun uu____430  ->
           match uu____430 with
           | (m,tds) ->
               FStar_Util.find_map tds
                 (fun uu____445  ->
                    match uu____445 with
                    | (uu____450,n1,mangle_opt,uu____453,uu____454) ->
>>>>>>> origin/guido_tactics
                        if m = mname
                        then
                          (if n1 = ty_name
                           then
                             match mangle_opt with
                             | None  -> Some (m, n1)
                             | Some mangled ->
                                 let modul = m in Some (modul, mangled)
                           else None)
                        else None))
let lookup_tyvar:
  env -> FStar_Syntax_Syntax.bv -> FStar_Extraction_ML_Syntax.mlty =
  fun g  -> fun bt  -> lookup_ty_local g.gamma bt
let lookup_fv_by_lid: env -> FStar_Ident.lident -> ty_or_exp_b =
  fun g  ->
    fun lid  ->
      let x =
        FStar_Util.find_map g.gamma
<<<<<<< HEAD
          (fun uu___103_456  ->
             match uu___103_456 with
             | Fv (fv',x) when FStar_Syntax_Syntax.fv_eq_lid fv' lid ->
                 Some x
             | uu____460 -> None) in
      match x with
      | None  ->
          let uu____461 =
            FStar_Util.format1 "free Variable %s not found\n"
              lid.FStar_Ident.nsstr in
          failwith uu____461
=======
          (fun uu___104_509  ->
             match uu___104_509 with
             | Fv (fv',x) when FStar_Syntax_Syntax.fv_eq_lid fv' lid ->
                 Some x
             | uu____513 -> None) in
      match x with
      | None  ->
          let uu____514 =
            FStar_Util.format1 "free Variable %s not found\n"
              lid.FStar_Ident.nsstr in
          failwith uu____514
>>>>>>> origin/guido_tactics
      | Some y -> y
let lookup_fv: env -> FStar_Syntax_Syntax.fv -> ty_or_exp_b =
  fun g  ->
    fun fv  ->
      let x =
        FStar_Util.find_map g.gamma
<<<<<<< HEAD
          (fun uu___104_474  ->
             match uu___104_474 with
             | Fv (fv',t) when FStar_Syntax_Syntax.fv_eq fv fv' -> Some t
             | uu____478 -> None) in
      match x with
      | None  ->
          let uu____479 =
            let uu____480 =
              FStar_Range.string_of_range
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.p in
            let uu____481 =
              FStar_Syntax_Print.lid_to_string
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            FStar_Util.format2 "(%s) free Variable %s not found\n" uu____480
              uu____481 in
          failwith uu____479
=======
          (fun uu___105_526  ->
             match uu___105_526 with
             | Fv (fv',t) when FStar_Syntax_Syntax.fv_eq fv fv' -> Some t
             | uu____530 -> None) in
      match x with
      | None  ->
          let uu____531 =
            let uu____532 =
              FStar_Range.string_of_range
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.p in
            let uu____537 =
              FStar_Syntax_Print.lid_to_string
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            FStar_Util.format2 "(%s) free Variable %s not found\n" uu____532
              uu____537 in
          failwith uu____531
>>>>>>> origin/guido_tactics
      | Some y -> y
let lookup_bv: env -> FStar_Syntax_Syntax.bv -> ty_or_exp_b =
  fun g  ->
    fun bv  ->
      let x =
        FStar_Util.find_map g.gamma
<<<<<<< HEAD
          (fun uu___105_494  ->
             match uu___105_494 with
             | Bv (bv',r) when FStar_Syntax_Syntax.bv_eq bv bv' -> Some r
             | uu____498 -> None) in
      match x with
      | None  ->
          let uu____499 =
            let uu____500 =
              FStar_Range.string_of_range
                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange in
            let uu____501 = FStar_Syntax_Print.bv_to_string bv in
            FStar_Util.format2 "(%s) bound Variable %s not found\n" uu____500
              uu____501 in
          failwith uu____499
=======
          (fun uu___106_553  ->
             match uu___106_553 with
             | Bv (bv',r) when FStar_Syntax_Syntax.bv_eq bv bv' -> Some r
             | uu____557 -> None) in
      match x with
      | None  ->
          let uu____558 =
            let uu____559 =
              FStar_Range.string_of_range
                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange in
            let uu____560 = FStar_Syntax_Print.bv_to_string bv in
            FStar_Util.format2 "(%s) bound Variable %s not found\n" uu____559
              uu____560 in
          failwith uu____558
>>>>>>> origin/guido_tactics
      | Some y -> y
let lookup:
  env ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
      (ty_or_exp_b* FStar_Syntax_Syntax.fv_qual option)
  =
  fun g  ->
    fun x  ->
      match x with
      | FStar_Util.Inl x1 ->
<<<<<<< HEAD
          let uu____520 = lookup_bv g x1 in (uu____520, None)
      | FStar_Util.Inr x1 ->
          let uu____523 = lookup_fv g x1 in
          (uu____523, (x1.FStar_Syntax_Syntax.fv_qual))
=======
          let uu____584 = lookup_bv g x1 in (uu____584, None)
      | FStar_Util.Inr x1 ->
          let uu____587 = lookup_fv g x1 in
          (uu____587, (x1.FStar_Syntax_Syntax.fv_qual))
>>>>>>> origin/guido_tactics
let lookup_term:
  env ->
    FStar_Syntax_Syntax.term ->
      (ty_or_exp_b* FStar_Syntax_Syntax.fv_qual option)
  =
  fun g  ->
    fun t  ->
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_name x -> lookup g (FStar_Util.Inl x)
      | FStar_Syntax_Syntax.Tm_fvar x -> lookup g (FStar_Util.Inr x)
<<<<<<< HEAD
      | uu____539 -> failwith "Impossible: lookup_term for a non-name"
=======
      | uu____605 -> failwith "Impossible: lookup_term for a non-name"
>>>>>>> origin/guido_tactics
let extend_ty:
  env ->
    FStar_Syntax_Syntax.bv -> FStar_Extraction_ML_Syntax.mlty option -> env
  =
  fun g  ->
    fun a  ->
      fun mapped_to  ->
        let ml_a = bv_as_ml_tyvar a in
        let mapped_to1 =
          match mapped_to with
          | None  -> FStar_Extraction_ML_Syntax.MLTY_Var ml_a
          | Some t -> t in
        let gamma = (Bv (a, (FStar_Util.Inl (ml_a, mapped_to1)))) ::
          (g.gamma) in
        let tcenv = FStar_TypeChecker_Env.push_bv g.tcenv a in
<<<<<<< HEAD
        let uu___107_582 = g in
        {
          tcenv;
          gamma;
          tydefs = (uu___107_582.tydefs);
          currentModule = (uu___107_582.currentModule)
=======
        let uu___108_651 = g in
        {
          tcenv;
          gamma;
          tydefs = (uu___108_651.tydefs);
          currentModule = (uu___108_651.currentModule)
>>>>>>> origin/guido_tactics
        }
let sanitize: Prims.string -> Prims.string =
  fun s  ->
    let cs = FStar_String.list_of_string s in
    let valid c =
      ((FStar_Util.is_letter_or_digit c) || (c = '_')) || (c = '\'') in
    let cs' =
      FStar_List.fold_right
        (fun c  ->
           fun cs1  ->
             let uu____668 =
               let uu____670 = valid c in
               if uu____670 then [c] else ['_'; '_'] in
             FStar_List.append uu____668 cs1) cs [] in
    let cs'1 =
      match cs' with
      | c::cs1 when (FStar_Util.is_digit c) || (c = '\'') -> '_' :: c :: cs1
      | uu____679 -> cs in
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
<<<<<<< HEAD
            (fun uu___106_606  ->
               match uu___106_606 with
               | Bv (uu____607,FStar_Util.Inl (mlident',uu____609)) ->
                   target_mlident = (fst mlident')
               | Fv (uu____624,FStar_Util.Inl (mlident',uu____626)) ->
                   target_mlident = (fst mlident')
               | Fv
                   (uu____641,FStar_Util.Inr
                    (mlident',uu____643,uu____644,uu____645))
                   -> target_mlident = mlident'
               | Bv
                   (uu____660,FStar_Util.Inr
                    (mlident',uu____662,uu____663,uu____664))
=======
            (fun uu___107_702  ->
               match uu___107_702 with
               | Bv (uu____703,FStar_Util.Inl (mlident',uu____705)) ->
                   target_mlident = (fst mlident')
               | Fv (uu____720,FStar_Util.Inl (mlident',uu____722)) ->
                   target_mlident = (fst mlident')
               | Fv
                   (uu____737,FStar_Util.Inr
                    (mlident',uu____739,uu____740,uu____741))
                   -> target_mlident = mlident'
               | Bv
                   (uu____756,FStar_Util.Inr
                    (mlident',uu____758,uu____759,uu____760))
>>>>>>> origin/guido_tactics
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
            Prims.bool -> (env* FStar_Extraction_ML_Syntax.mlident)
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
<<<<<<< HEAD
                | uu____705 -> FStar_Extraction_ML_Syntax.MLTY_Top in
              let uu____706 = FStar_Extraction_ML_Syntax.bv_as_mlident x in
              match uu____706 with
=======
                | uu____808 -> FStar_Extraction_ML_Syntax.MLTY_Top in
              let uu____809 = FStar_Extraction_ML_Syntax.bv_as_mlident x in
              match uu____809 with
>>>>>>> origin/guido_tactics
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
                  let gamma =
                    (Bv (x, (FStar_Util.Inr (mlsymbol, mlx1, t_x, is_rec))))
                    :: (g.gamma) in
                  let tcenv =
<<<<<<< HEAD
                    let uu____737 = FStar_Syntax_Syntax.binders_of_list [x] in
                    FStar_TypeChecker_Env.push_binders g.tcenv uu____737 in
                  ((let uu___108_741 = g in
                    {
                      tcenv;
                      gamma;
                      tydefs = (uu___108_741.tydefs);
                      currentModule = (uu___108_741.currentModule)
=======
                    let uu____840 = FStar_Syntax_Syntax.binders_of_list [x] in
                    FStar_TypeChecker_Env.push_binders g.tcenv uu____840 in
                  ((let uu___109_843 = g in
                    {
                      tcenv;
                      gamma;
                      tydefs = (uu___109_843.tydefs);
                      currentModule = (uu___109_843.currentModule)
>>>>>>> origin/guido_tactics
                    }), mlident1)
let rec mltyFvars:
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlident Prims.list
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Var x -> [x]
    | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,f,t2) ->
<<<<<<< HEAD
        let uu____751 = mltyFvars t1 in
        let uu____753 = mltyFvars t2 in FStar_List.append uu____751 uu____753
=======
        let uu____855 = mltyFvars t1 in
        let uu____857 = mltyFvars t2 in FStar_List.append uu____855 uu____857
>>>>>>> origin/guido_tactics
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
<<<<<<< HEAD
    let uu____777 = mltyFvars (snd tys) in subsetMlidents uu____777 (fst tys)
=======
    let uu____884 = mltyFvars (snd tys) in subsetMlidents uu____884 (fst tys)
>>>>>>> origin/guido_tactics
let extend_fv':
  env ->
    FStar_Syntax_Syntax.fv ->
      FStar_Extraction_ML_Syntax.mlpath ->
        FStar_Extraction_ML_Syntax.mltyscheme ->
          Prims.bool ->
            Prims.bool -> (env* FStar_Extraction_ML_Syntax.mlident)
  =
  fun g  ->
    fun x  ->
      fun y  ->
        fun t_x  ->
          fun add_unit  ->
            fun is_rec  ->
<<<<<<< HEAD
              let uu____801 = tySchemeIsClosed t_x in
              if uu____801
=======
              let uu____914 = tySchemeIsClosed t_x in
              if uu____914
>>>>>>> origin/guido_tactics
              then
                let ml_ty =
                  match t_x with
                  | ([],t) -> t
<<<<<<< HEAD
                  | uu____807 -> FStar_Extraction_ML_Syntax.MLTY_Top in
                let uu____808 =
                  let uu____814 = y in
                  match uu____814 with
=======
                  | uu____920 -> FStar_Extraction_ML_Syntax.MLTY_Top in
                let uu____921 =
                  let uu____927 = y in
                  match uu____927 with
>>>>>>> origin/guido_tactics
                  | (ns,i) ->
                      let mlsymbol =
                        FStar_Extraction_ML_Syntax.avoid_keyword i in
                      ((ns, mlsymbol), mlsymbol) in
<<<<<<< HEAD
                match uu____808 with
=======
                match uu____921 with
>>>>>>> origin/guido_tactics
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
                    let gamma =
                      (Fv (x, (FStar_Util.Inr (mlsymbol, mly1, t_x, is_rec))))
                      :: (g.gamma) in
<<<<<<< HEAD
                    ((let uu___109_862 = g in
                      {
                        tcenv = (uu___109_862.tcenv);
                        gamma;
                        tydefs = (uu___109_862.tydefs);
                        currentModule = (uu___109_862.currentModule)
=======
                    ((let uu___110_974 = g in
                      {
                        tcenv = (uu___110_974.tcenv);
                        gamma;
                        tydefs = (uu___110_974.tydefs);
                        currentModule = (uu___110_974.currentModule)
>>>>>>> origin/guido_tactics
                      }), (mlsymbol, (Prims.parse_int "0")))
              else failwith "freevars found"
let extend_fv:
  env ->
    FStar_Syntax_Syntax.fv ->
      FStar_Extraction_ML_Syntax.mltyscheme ->
        Prims.bool -> Prims.bool -> (env* FStar_Extraction_ML_Syntax.mlident)
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
            Prims.bool -> (env* FStar_Extraction_ML_Syntax.mlident)
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
<<<<<<< HEAD
                  let uu____910 =
                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                      (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  (match uu____910 with
=======
                  let uu____1039 =
                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                      (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  (match uu____1039 with
>>>>>>> origin/guido_tactics
                   | (p,y) -> extend_fv' g f (p, y) t_x add_unit is_rec)
let extend_tydef:
  env -> FStar_Syntax_Syntax.fv -> FStar_Extraction_ML_Syntax.mltydecl -> env
  =
  fun g  ->
    fun fv  ->
      fun td  ->
        let m = module_name_of_fv fv in
<<<<<<< HEAD
        let uu___110_929 = g in
        {
          tcenv = (uu___110_929.tcenv);
          gamma = (uu___110_929.gamma);
          tydefs = ((m, td) :: (g.tydefs));
          currentModule = (uu___110_929.currentModule)
=======
        let uu___111_1065 = g in
        {
          tcenv = (uu___111_1065.tcenv);
          gamma = (uu___111_1065.gamma);
          tydefs = ((m, td) :: (g.tydefs));
          currentModule = (uu___111_1065.currentModule)
>>>>>>> origin/guido_tactics
        }
let emptyMlPath:
  (FStar_Extraction_ML_Syntax.mlsymbol Prims.list* Prims.string) = ([], "")
let mkContext: FStar_TypeChecker_Env.env -> env =
  fun e  ->
    let env =
      { tcenv = e; gamma = []; tydefs = []; currentModule = emptyMlPath } in
    let a = ("'a", (- (Prims.parse_int "1"))) in
    let failwith_ty =
      ([a],
        (FStar_Extraction_ML_Syntax.MLTY_Fun
           ((FStar_Extraction_ML_Syntax.MLTY_Named
               ([], (["Prims"], "string"))),
             FStar_Extraction_ML_Syntax.E_IMPURE,
             (FStar_Extraction_ML_Syntax.MLTY_Var a)))) in
<<<<<<< HEAD
    let uu____966 =
      let uu____969 =
        let uu____970 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.failwith_lid
            FStar_Syntax_Syntax.Delta_constant None in
        FStar_Util.Inr uu____970 in
      extend_lb env uu____969 FStar_Syntax_Syntax.tun failwith_ty false false in
    FStar_All.pipe_right uu____966 FStar_Pervasives.fst
=======
    let uu____1103 =
      let uu____1106 =
        let uu____1107 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.failwith_lid
            FStar_Syntax_Syntax.Delta_constant None in
        FStar_Util.Inr uu____1107 in
      extend_lb env uu____1106 FStar_Syntax_Syntax.tun failwith_ty false
        false in
    FStar_All.pipe_right uu____1103 FStar_Pervasives.fst
>>>>>>> origin/guido_tactics
let monad_op_name:
  FStar_Syntax_Syntax.eff_decl ->
    Prims.string -> (FStar_Extraction_ML_Syntax.mlpath* FStar_Ident.lident)
  =
  fun ed  ->
    fun nm  ->
      let lid =
        FStar_Syntax_Util.mk_field_projector_name_from_ident
          ed.FStar_Syntax_Syntax.mname (FStar_Ident.id_of_text nm) in
<<<<<<< HEAD
      let uu____982 = FStar_Extraction_ML_Syntax.mlpath_of_lident lid in
      (uu____982, lid)
=======
      let uu____1121 = FStar_Extraction_ML_Syntax.mlpath_of_lident lid in
      (uu____1121, lid)
>>>>>>> origin/guido_tactics
let action_name:
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.action ->
      (FStar_Extraction_ML_Syntax.mlpath* FStar_Ident.lident)
  =
  fun ed  ->
    fun a  ->
      let nm =
        ((a.FStar_Syntax_Syntax.action_name).FStar_Ident.ident).FStar_Ident.idText in
      let module_name = (ed.FStar_Syntax_Syntax.mname).FStar_Ident.ns in
      let lid =
        FStar_Ident.lid_of_ids
          (FStar_List.append module_name [FStar_Ident.id_of_text nm]) in
<<<<<<< HEAD
      let uu____995 = FStar_Extraction_ML_Syntax.mlpath_of_lident lid in
      (uu____995, lid)
=======
      let uu____1136 = FStar_Extraction_ML_Syntax.mlpath_of_lident lid in
      (uu____1136, lid)
>>>>>>> origin/guido_tactics

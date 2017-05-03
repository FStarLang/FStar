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
  fun projectee  -> match projectee with | Bv _0 -> true | uu____25 -> false
let __proj__Bv__item___0: binding -> (FStar_Syntax_Syntax.bv* ty_or_exp_b) =
  fun projectee  -> match projectee with | Bv _0 -> _0
let uu___is_Fv: binding -> Prims.bool =
  fun projectee  -> match projectee with | Fv _0 -> true | uu____45 -> false
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
let debug: env -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun g  ->
    fun f  ->
      let c = FStar_Extraction_ML_Syntax.string_of_mlpath g.currentModule in
      let uu____114 =
        FStar_Options.debug_at_level c (FStar_Options.Other "Extraction") in
      if uu____114 then f () else ()
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
           (uu____126,("FStar"::"Ghost"::[],"erased")) -> true
       | uu____133 -> false)
let unknownType: FStar_Extraction_ML_Syntax.mlty =
  FStar_Extraction_ML_Syntax.MLTY_Top
let prependTick uu____144 =
  match uu____144 with
  | (x,n1) ->
      if FStar_Util.starts_with x "'"
      then (x, n1)
      else ((Prims.strcat "'A" x), n1)
let removeTick uu____162 =
  match uu____162 with
  | (x,n1) ->
      if FStar_Util.starts_with x "'"
      then
        let uu____169 = FStar_Util.substring_from x (Prims.parse_int "1") in
        (uu____169, n1)
      else (x, n1)
let convRange: FStar_Range.range -> Prims.int = fun r  -> Prims.parse_int "0"
let convIdent: FStar_Ident.ident -> (Prims.string* Prims.int) =
  fun id  -> ((id.FStar_Ident.idText), (Prims.parse_int "0"))
let bv_as_ml_tyvar: FStar_Syntax_Syntax.bv -> (Prims.string* Prims.int) =
  fun x  ->
    let uu____182 = FStar_Extraction_ML_Syntax.bv_as_mlident x in
    prependTick uu____182
let bv_as_ml_termvar: FStar_Syntax_Syntax.bv -> (Prims.string* Prims.int) =
  fun x  ->
    let uu____190 = FStar_Extraction_ML_Syntax.bv_as_mlident x in
    removeTick uu____190
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
      | (Bv (b',FStar_Util.Inr uu____222))::tl1 ->
          if FStar_Syntax_Syntax.bv_eq b b'
          then
            failwith
              (Prims.strcat "Type/Expr clash: "
                 (b.FStar_Syntax_Syntax.ppname).FStar_Ident.idText)
          else lookup_ty_local tl1 b
      | uu____244::tl1 -> lookup_ty_local tl1 b
      | [] ->
          failwith
            (Prims.strcat "extraction: unbound type var "
               (b.FStar_Syntax_Syntax.ppname).FStar_Ident.idText)
let tyscheme_of_td uu____264 =
  match uu____264 with
  | (uu____271,uu____272,uu____273,vars,body_opt) ->
      (match body_opt with
       | Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev t) -> Some (vars, t)
       | uu____283 -> None)
let lookup_ty_const:
  env ->
    FStar_Extraction_ML_Syntax.mlpath ->
      FStar_Extraction_ML_Syntax.mltyscheme Prims.option
  =
  fun env  ->
    fun uu____291  ->
      match uu____291 with
      | (module_name,ty_name) ->
          FStar_Util.find_map env.tydefs
            (fun uu____301  ->
               match uu____301 with
               | (m,tds) ->
                   if module_name = m
                   then
                     FStar_Util.find_map tds
                       (fun td  ->
                          let uu____313 = td in
                          match uu____313 with
                          | (uu____315,n1,uu____317,uu____318,uu____319) ->
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
        FStar_Extraction_ML_Syntax.mlsymbol) Prims.option
  =
  fun env  ->
    fun fv  ->
      let mname = module_name_of_fv fv in
      let ty_name =
        (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText in
      FStar_Util.find_map env.tydefs
        (fun uu____360  ->
           match uu____360 with
           | (m,tds) ->
               FStar_Util.find_map tds
                 (fun uu____375  ->
                    match uu____375 with
                    | (uu____380,n1,mangle_opt,uu____383,uu____384) ->
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
let lookup_eff_action:
  env ->
    (FStar_Syntax_Syntax.fv,FStar_Ident.lident) FStar_Util.either ->
      ty_or_exp_b
  =
  fun g  ->
    fun x  ->
      let uu____437 =
        match x with
        | FStar_Util.Inl fv ->
            let uu____443 =
              FStar_Range.string_of_range
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.p in
            (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v),
              uu____443)
        | FStar_Util.Inr lid ->
            let uu____453 =
              FStar_Range.string_of_range FStar_Range.dummyRange in
            (lid, uu____453) in
      match uu____437 with
      | (name,range) ->
          let fv_not_found =
            let uu____457 = FStar_Syntax_Print.lid_to_string name in
            FStar_Util.format2 "(%s) free Variable %s not found\n" range
              uu____457 in
          let eff_name =
            let idents =
              FStar_String.split ['_']
                (name.FStar_Ident.ident).FStar_Ident.idText in
            try
              let uu____462 =
                let uu____465 =
                  FStar_List.index (fun x1  -> x1 = "proj") idents in
                let uu____467 =
                  FStar_List.index (fun x1  -> x1 = "item") idents in
                (uu____465, uu____467) in
              match uu____462 with
              | (i,j) ->
                  let uu____471 =
                    let uu____473 =
                      let uu____478 =
                        let uu____480 =
                          FStar_List.splitAt (j - (Prims.parse_int "1"))
                            idents in
                        Prims.fst uu____480 in
                      FStar_List.splitAt (i + (Prims.parse_int "2"))
                        uu____478 in
                    Prims.snd uu____473 in
                  FStar_All.pipe_left (FStar_String.concat "_") uu____471
            with | uu____491 -> failwith fv_not_found in
          let action_name =
            let uu____493 =
              let uu____495 =
                FStar_List.map (fun x1  -> x1.FStar_Ident.idText)
                  name.FStar_Ident.ns in
              FStar_List.append uu____495
                [eff_name; (name.FStar_Ident.ident).FStar_Ident.idText] in
            FStar_All.pipe_left (FStar_String.concat ".") uu____493 in
          let x1 =
            FStar_Util.find_map g.gamma
              (fun uu___108_501  ->
                 match uu___108_501 with
                 | Fv (fv',t) when
                     ((fv'.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.str
                       = action_name
                     -> Some t
                 | uu____509 -> None) in
          (match x1 with | None  -> failwith fv_not_found | Some y -> y)
let lookup_fv_by_lid: env -> FStar_Ident.lident -> ty_or_exp_b =
  fun g  ->
    fun lid  ->
      let x =
        FStar_Util.find_map g.gamma
          (fun uu___109_519  ->
             match uu___109_519 with
             | Fv (fv',x) when FStar_Syntax_Syntax.fv_eq_lid fv' lid ->
                 Some x
             | uu____523 -> None) in
      match x with
      | None  -> lookup_eff_action g (FStar_Util.Inr lid)
      | Some y -> y
let lookup_fv: env -> FStar_Syntax_Syntax.fv -> ty_or_exp_b =
  fun g  ->
    fun fv  ->
      let x =
        FStar_Util.find_map g.gamma
          (fun uu___110_533  ->
             match uu___110_533 with
             | Fv (fv',t) when FStar_Syntax_Syntax.fv_eq fv fv' -> Some t
             | uu____537 -> None) in
      match x with
      | None  -> lookup_eff_action g (FStar_Util.Inl fv)
      | Some y -> y
let lookup_bv: env -> FStar_Syntax_Syntax.bv -> ty_or_exp_b =
  fun g  ->
    fun bv  ->
      let x =
        FStar_Util.find_map g.gamma
          (fun uu___111_547  ->
             match uu___111_547 with
             | Bv (bv',r) when FStar_Syntax_Syntax.bv_eq bv bv' -> Some r
             | uu____551 -> None) in
      match x with
      | None  ->
          let uu____552 =
            let uu____553 =
              FStar_Range.string_of_range
                (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange in
            let uu____554 = FStar_Syntax_Print.bv_to_string bv in
            FStar_Util.format2 "(%s) bound Variable %s not found\n" uu____553
              uu____554 in
          failwith uu____552
      | Some y -> y
let lookup:
  env ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
      (ty_or_exp_b* FStar_Syntax_Syntax.fv_qual Prims.option)
  =
  fun g  ->
    fun x  ->
      match x with
      | FStar_Util.Inl x1 ->
          let uu____576 = lookup_bv g x1 in (uu____576, None)
      | FStar_Util.Inr x1 ->
          let uu____579 = lookup_fv g x1 in
          (uu____579, (x1.FStar_Syntax_Syntax.fv_qual))
let lookup_term:
  env ->
    FStar_Syntax_Syntax.term ->
      (ty_or_exp_b* FStar_Syntax_Syntax.fv_qual Prims.option)
  =
  fun g  ->
    fun t  ->
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_name x -> lookup g (FStar_Util.Inl x)
      | FStar_Syntax_Syntax.Tm_fvar x -> lookup g (FStar_Util.Inr x)
      | uu____595 -> failwith "Impossible: lookup_term for a non-name"
let extend_ty:
  env ->
    FStar_Syntax_Syntax.bv ->
      FStar_Extraction_ML_Syntax.mlty Prims.option -> env
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
        let uu___115_638 = g in
        {
          tcenv;
          gamma;
          tydefs = (uu___115_638.tydefs);
          currentModule = (uu___115_638.currentModule)
        }
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
            (fun uu___112_658  ->
               match uu___112_658 with
               | Bv (_,FStar_Util.Inl (mlident',_))|Fv
                 (_,FStar_Util.Inl (mlident',_)) ->
                   target_mlident = (Prims.fst mlident')
               | Fv (_,FStar_Util.Inr (mlident',_,_,_))|Bv
                 (_,FStar_Util.Inr (mlident',_,_,_)) ->
                   target_mlident = mlident') gamma in
        if has_collision
        then find_uniq mlident1 (i + (Prims.parse_int "1"))
        else target_mlident in
      find_uniq mlident (Prims.parse_int "0")
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
                | uu____755 -> FStar_Extraction_ML_Syntax.MLTY_Top in
              let uu____756 = FStar_Extraction_ML_Syntax.bv_as_mlident x in
              match uu____756 with
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
                    let uu____787 = FStar_Syntax_Syntax.binders_of_list [x] in
                    FStar_TypeChecker_Env.push_binders g.tcenv uu____787 in
                  ((let uu___116_790 = g in
                    {
                      tcenv;
                      gamma;
                      tydefs = (uu___116_790.tydefs);
                      currentModule = (uu___116_790.currentModule)
                    }), mlident1)
let rec mltyFvars:
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlident Prims.list
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Var x -> [x]
    | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,f,t2) ->
        let uu____801 = mltyFvars t1 in
        let uu____803 = mltyFvars t2 in FStar_List.append uu____801 uu____803
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
    let uu____827 = mltyFvars (Prims.snd tys) in
    subsetMlidents uu____827 (Prims.fst tys)
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
              let uu____851 = tySchemeIsClosed t_x in
              if uu____851
              then
                let ml_ty =
                  match t_x with
                  | ([],t) -> t
                  | uu____857 -> FStar_Extraction_ML_Syntax.MLTY_Top in
                let uu____858 =
                  let uu____864 = y in
                  match uu____864 with
                  | (ns,i) ->
                      let mlsymbol =
                        FStar_Extraction_ML_Syntax.avoid_keyword i in
                      ((ns, mlsymbol), mlsymbol) in
                match uu____858 with
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
                    ((let uu___117_911 = g in
                      {
                        tcenv = (uu___117_911.tcenv);
                        gamma;
                        tydefs = (uu___117_911.tydefs);
                        currentModule = (uu___117_911.currentModule)
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
                  let uu____965 =
                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                      (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  (match uu____965 with
                   | (p,y) -> extend_fv' g f (p, y) t_x add_unit is_rec)
let extend_tydef:
  env -> FStar_Syntax_Syntax.fv -> FStar_Extraction_ML_Syntax.mltydecl -> env
  =
  fun g  ->
    fun fv  ->
      fun td  ->
        let m = module_name_of_fv fv in
        let uu___118_988 = g in
        {
          tcenv = (uu___118_988.tcenv);
          gamma = (uu___118_988.gamma);
          tydefs = ((m, td) :: (g.tydefs));
          currentModule = (uu___118_988.currentModule)
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
    let uu____1025 =
      let uu____1028 =
        let uu____1029 =
          FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.failwith_lid
            FStar_Syntax_Syntax.Delta_constant None in
        FStar_Util.Inr uu____1029 in
      extend_lb env uu____1028 FStar_Syntax_Syntax.tun failwith_ty false
        false in
    FStar_All.pipe_right uu____1025 Prims.fst
let monad_op_name:
  FStar_Syntax_Syntax.eff_decl ->
    Prims.string -> (FStar_Extraction_ML_Syntax.mlpath* FStar_Ident.lident)
  =
  fun ed  ->
    fun nm  ->
      let uu____1040 =
        (((ed.FStar_Syntax_Syntax.mname).FStar_Ident.ns),
          ((ed.FStar_Syntax_Syntax.mname).FStar_Ident.ident)) in
      match uu____1040 with
      | (module_name,eff_name) ->
          let mangled_name =
            Prims.strcat FStar_Ident.reserved_prefix
              (Prims.strcat eff_name.FStar_Ident.idText (Prims.strcat "_" nm)) in
          let mangled_lid =
            FStar_Ident.lid_of_ids
              (FStar_List.append module_name
                 [FStar_Ident.id_of_text mangled_name]) in
          let ml_name =
            FStar_Extraction_ML_Syntax.mlpath_of_lident mangled_lid in
          let lid =
            FStar_All.pipe_right
              (FStar_List.append
                 (FStar_Ident.ids_of_lid ed.FStar_Syntax_Syntax.mname)
                 [FStar_Ident.id_of_text nm]) FStar_Ident.lid_of_ids in
          (ml_name, lid)
let action_name:
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.action ->
      (FStar_Extraction_ML_Syntax.mlpath* FStar_Ident.lident)
  =
  fun ed  ->
    fun a  ->
      monad_op_name ed
        ((a.FStar_Syntax_Syntax.action_name).FStar_Ident.ident).FStar_Ident.idText
let bind_name:
  FStar_Syntax_Syntax.eff_decl ->
    (FStar_Extraction_ML_Syntax.mlpath* FStar_Ident.lident)
  = fun ed  -> monad_op_name ed "bind"
let return_name:
  FStar_Syntax_Syntax.eff_decl ->
    (FStar_Extraction_ML_Syntax.mlpath* FStar_Ident.lident)
  = fun ed  -> monad_op_name ed "return"
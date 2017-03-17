open Prims
type ty_or_exp_b =
  ((FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty),
    (FStar_Extraction_ML_Syntax.mlexpr *
      FStar_Extraction_ML_Syntax.mltyscheme * Prims.bool))
    FStar_Util.either
type binding =
  | Bv of (FStar_Syntax_Syntax.bv * ty_or_exp_b) 
  | Fv of (FStar_Syntax_Syntax.fv * ty_or_exp_b) 
let uu___is_Bv : binding -> Prims.bool =
  fun projectee  -> match projectee with | Bv _0 -> true | uu____24 -> false 
let __proj__Bv__item___0 : binding -> (FStar_Syntax_Syntax.bv * ty_or_exp_b)
  = fun projectee  -> match projectee with | Bv _0 -> _0 
let uu___is_Fv : binding -> Prims.bool =
  fun projectee  -> match projectee with | Fv _0 -> true | uu____44 -> false 
let __proj__Fv__item___0 : binding -> (FStar_Syntax_Syntax.fv * ty_or_exp_b)
  = fun projectee  -> match projectee with | Fv _0 -> _0 
type env =
  {
  tcenv: FStar_TypeChecker_Env.env ;
  gamma: binding Prims.list ;
  tydefs:
    (FStar_Extraction_ML_Syntax.mlsymbol Prims.list *
      FStar_Extraction_ML_Syntax.mltydecl) Prims.list
    ;
  currentModule: FStar_Extraction_ML_Syntax.mlpath }
let debug : env -> (Prims.unit -> Prims.unit) -> Prims.unit =
  fun g  ->
    fun f  ->
      let c = FStar_Extraction_ML_Syntax.string_of_mlpath g.currentModule  in
      let uu____113 =
        FStar_Options.debug_at_level c (FStar_Options.Other "Extraction")  in
      match uu____113 with | true  -> f () | uu____114 -> ()
  
let mkFvvar :
  FStar_Ident.lident -> FStar_Syntax_Syntax.typ -> FStar_Syntax_Syntax.fv =
  fun l  ->
    fun t  ->
      FStar_Syntax_Syntax.lid_as_fv l FStar_Syntax_Syntax.Delta_constant None
  
let erasedContent : FStar_Extraction_ML_Syntax.mlty =
  FStar_Extraction_ML_Syntax.ml_unit_ty 
let erasableTypeNoDelta : FStar_Extraction_ML_Syntax.mlty -> Prims.bool =
  fun t  ->
    match t = FStar_Extraction_ML_Syntax.ml_unit_ty with
    | true  -> true
    | uu____124 ->
        (match t with
         | FStar_Extraction_ML_Syntax.MLTY_Named
             (uu____125,("FStar"::"Ghost"::[],"erased")) -> true
         | uu____132 -> false)
  
let unknownType : FStar_Extraction_ML_Syntax.mlty =
  FStar_Extraction_ML_Syntax.MLTY_Top 
let prependTick uu____143 =
  match uu____143 with
  | (x,n) ->
      (match FStar_Util.starts_with x "'" with
       | true  -> (x, n)
       | uu____150 -> ((Prims.strcat "'A" x), n))
  
let removeTick uu____161 =
  match uu____161 with
  | (x,n) ->
      (match FStar_Util.starts_with x "'" with
       | true  ->
           let _0_171 = FStar_Util.substring_from x (Prims.parse_int "1")  in
           (_0_171, n)
       | uu____168 -> (x, n))
  
let convRange : FStar_Range.range -> Prims.int =
  fun r  -> (Prims.parse_int "0") 
let convIdent : FStar_Ident.ident -> (Prims.string * Prims.int) =
  fun id  -> ((id.FStar_Ident.idText), (Prims.parse_int "0")) 
let bv_as_ml_tyvar : FStar_Syntax_Syntax.bv -> (Prims.string * Prims.int) =
  fun x  -> prependTick (FStar_Extraction_ML_Syntax.bv_as_mlident x) 
let bv_as_ml_termvar : FStar_Syntax_Syntax.bv -> (Prims.string * Prims.int) =
  fun x  -> removeTick (FStar_Extraction_ML_Syntax.bv_as_mlident x) 
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
  
let tyscheme_of_td uu____251 =
  match uu____251 with
  | (uu____258,uu____259,uu____260,vars,body_opt) ->
      (match body_opt with
       | Some (FStar_Extraction_ML_Syntax.MLTD_Abbrev t) -> Some (vars, t)
       | uu____270 -> None)
  
let lookup_ty_const :
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
                   (match module_name = m with
                    | true  ->
                        FStar_Util.find_map tds
                          (fun td  ->
                             let uu____300 = td  in
                             match uu____300 with
                             | (uu____302,n,uu____304,uu____305,uu____306) ->
                                 (match n = ty_name with
                                  | true  -> tyscheme_of_td td
                                  | uu____313 -> None))
                    | uu____314 -> None))
  
let module_name_of_fv : FStar_Syntax_Syntax.fv -> Prims.string Prims.list =
  fun fv  ->
    FStar_All.pipe_right
      ((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ns
      (FStar_List.map (fun i  -> i.FStar_Ident.idText))
  
let maybe_mangle_type_projector :
  env ->
    FStar_Syntax_Syntax.fv ->
      (FStar_Extraction_ML_Syntax.mlsymbol Prims.list *
        FStar_Extraction_ML_Syntax.mlsymbol) Prims.option
  =
  fun env  ->
    fun fv  ->
      let mname = module_name_of_fv fv  in
      let ty_name =
        (((fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v).FStar_Ident.ident).FStar_Ident.idText
         in
      FStar_Util.find_map env.tydefs
        (fun uu____360  ->
           match uu____360 with
           | (m,tds) ->
               FStar_Util.find_map tds
                 (fun uu____362  ->
                    match uu____362 with
                    | (uu____367,n,mangle_opt,uu____370,uu____371) ->
                        (match m = mname with
                         | true  ->
                             (match n = ty_name with
                              | true  ->
                                  (match mangle_opt with
                                   | None  -> Some (m, n)
                                   | Some mangled ->
                                       let modul = m  in
                                       Some (modul, mangled))
                              | uu____400 -> None)
                         | uu____404 -> None)))
  
let lookup_tyvar :
  env -> FStar_Syntax_Syntax.bv -> FStar_Extraction_ML_Syntax.mlty =
  fun g  -> fun bt  -> lookup_ty_local g.gamma bt 
let lookup_fv_by_lid : env -> FStar_Ident.lident -> ty_or_exp_b =
  fun g  ->
    fun lid  ->
      let x =
        FStar_Util.find_map g.gamma
          (fun uu___102_435  ->
             match uu___102_435 with
             | Fv (fv',x) when FStar_Syntax_Syntax.fv_eq_lid fv' lid ->
                 Some x
             | uu____426 -> None)
         in
      match x with
      | None  ->
          let uu____440 =
            FStar_Util.format1 "free Variable %s not found\n"
              lid.FStar_Ident.nsstr in
          failwith uu____440
      | Some y -> y
  
let lookup_fv : env -> FStar_Syntax_Syntax.fv -> ty_or_exp_b =
  fun g  ->
    fun fv  ->
      let x =
        FStar_Util.find_map g.gamma
          (fun uu___103_450  ->
             match uu___103_450 with
             | Fv (fv',t) when FStar_Syntax_Syntax.fv_eq fv fv' -> Some t
             | uu____440 -> None)
         in
      match x with
      | None  ->
          failwith
            (let _0_173 =
               FStar_Range.string_of_range
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.p
                in
             let _0_172 =
               FStar_Syntax_Print.lid_to_string
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                in
             FStar_Util.format2 "(%s) free Variable %s not found\n" _0_173
               _0_172)
      | Some y -> y
  
let lookup_bv : env -> FStar_Syntax_Syntax.bv -> ty_or_exp_b =
  fun g  ->
    fun bv  ->
      let x =
        FStar_Util.find_map g.gamma
          (fun uu___104_475  ->
             match uu___104_475 with
             | Bv (bv',r) when FStar_Syntax_Syntax.bv_eq bv bv' -> Some r
             | uu____462 -> None)
         in
      match x with
      | None  ->
          failwith
            (let _0_175 =
               FStar_Range.string_of_range
                 (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idRange
                in
             let _0_174 = FStar_Syntax_Print.bv_to_string bv  in
             FStar_Util.format2 "(%s) bound Variable %s not found\n" _0_175
               _0_174)
      | Some y -> y
  
let lookup :
  env ->
    (FStar_Syntax_Syntax.bv,FStar_Syntax_Syntax.fv) FStar_Util.either ->
      (ty_or_exp_b * FStar_Syntax_Syntax.fv_qual Prims.option)
  =
  fun g  ->
    fun x  ->
      match x with
      | FStar_Util.Inl x -> let _0_176 = lookup_bv g x  in (_0_176, None)
      | FStar_Util.Inr x ->
          let _0_177 = lookup_fv g x  in
          (_0_177, (x.FStar_Syntax_Syntax.fv_qual))
  
let lookup_term :
  env ->
    FStar_Syntax_Syntax.term ->
      (ty_or_exp_b * FStar_Syntax_Syntax.fv_qual Prims.option)
  =
  fun g  ->
    fun t  ->
      match t.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_name x -> lookup g (FStar_Util.Inl x)
      | FStar_Syntax_Syntax.Tm_fvar x -> lookup g (FStar_Util.Inr x)
      | uu____501 -> failwith "Impossible: lookup_term for a non-name"
  
let extend_ty :
  env ->
    FStar_Syntax_Syntax.bv ->
      FStar_Extraction_ML_Syntax.mlty Prims.option -> env
  =
  fun g  ->
    fun a  ->
      fun mapped_to  ->
        let ml_a = bv_as_ml_tyvar a  in
        let mapped_to =
          match mapped_to with
          | None  -> FStar_Extraction_ML_Syntax.MLTY_Var ml_a
          | Some t -> t  in
        let gamma = (Bv (a, (FStar_Util.Inl (ml_a, mapped_to)))) :: (g.gamma)
           in
        let tcenv = FStar_TypeChecker_Env.push_bv g.tcenv a  in
        let uu___103_542 = g  in
        {
          tcenv;
          gamma;
          tydefs = (uu___106_566.tydefs);
          currentModule = (uu___106_566.currentModule)
        }
  
let extend_bv :
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
                | uu____564 -> FStar_Extraction_ML_Syntax.MLTY_Top  in
              let mlx =
                FStar_Extraction_ML_Syntax.MLE_Var
                  (FStar_Extraction_ML_Syntax.bv_as_mlident x)
                 in
              let mlx =
                match mk_unit with
                | true  -> FStar_Extraction_ML_Syntax.ml_unit
                | uu____567 ->
                    (match add_unit with
                     | true  ->
                         FStar_All.pipe_left
                           (FStar_Extraction_ML_Syntax.with_ty
                              FStar_Extraction_ML_Syntax.MLTY_Top)
                           (FStar_Extraction_ML_Syntax.MLE_App
                              ((FStar_Extraction_ML_Syntax.with_ty
                                  FStar_Extraction_ML_Syntax.MLTY_Top mlx),
                                [FStar_Extraction_ML_Syntax.ml_unit]))
                     | uu____569 ->
                         FStar_Extraction_ML_Syntax.with_ty ml_ty mlx)
                 in
              let gamma = (Bv (x, (FStar_Util.Inr (mlx, t_x, is_rec)))) ::
                (g.gamma)  in
              let tcenv =
                let _0_178 = FStar_Syntax_Syntax.binders_of_list [x]  in
                FStar_TypeChecker_Env.push_binders g.tcenv _0_178  in
              let uu___104_585 = g  in
              {
                tcenv;
                gamma;
                tydefs = (uu___104_585.tydefs);
                currentModule = (uu___104_585.currentModule)
              }
  
let rec mltyFvars :
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlident Prims.list
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Var x -> [x]
    | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,f,t2) ->
        let _0_180 = mltyFvars t1  in
        let _0_179 = mltyFvars t2  in FStar_List.append _0_180 _0_179
    | FStar_Extraction_ML_Syntax.MLTY_Named (args,path) ->
        FStar_List.collect mltyFvars args
    | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
        FStar_List.collect mltyFvars ts
    | FStar_Extraction_ML_Syntax.MLTY_Top  -> []
  
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
    let _0_181 = mltyFvars (Prims.snd tys)  in
    subsetMlidents _0_181 (Prims.fst tys)
  
let extend_fv' :
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
              let uu____636 = tySchemeIsClosed t_x  in
              match uu____636 with
              | true  ->
                  let ml_ty =
                    match t_x with
                    | ([],t) -> t
                    | uu____640 -> FStar_Extraction_ML_Syntax.MLTY_Top  in
                  let mly =
                    FStar_Extraction_ML_Syntax.MLE_Name
                      (let uu____642 = y  in
                       match uu____642 with
                       | (ns,i) ->
                           (ns, (FStar_Extraction_ML_Syntax.avoid_keyword i)))
                     in
                  let mly =
                    match add_unit with
                    | true  ->
                        FStar_All.pipe_left
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top)
                          (FStar_Extraction_ML_Syntax.MLE_App
                             ((FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.MLTY_Top mly),
                               [FStar_Extraction_ML_Syntax.ml_unit]))
                    | uu____650 ->
                        FStar_Extraction_ML_Syntax.with_ty ml_ty mly
                     in
                  let gamma = (Fv (x, (FStar_Util.Inr (mly, t_x, is_rec))))
                    :: (g.gamma)  in
                  let uu___105_665 = g  in
                  {
                    tcenv = (uu___105_665.tcenv);
                    gamma;
                    tydefs = (uu___105_665.tydefs);
                    currentModule = (uu___105_665.currentModule)
                  }
              | uu____666 -> failwith "freevars found"
  
let extend_fv :
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
                (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            extend_fv' g x mlp t_x add_unit is_rec
  
let extend_lb :
  env ->
    FStar_Syntax_Syntax.lbname ->
      FStar_Syntax_Syntax.typ ->
        FStar_Extraction_ML_Syntax.mltyscheme ->
          Prims.bool ->
            Prims.bool -> (env * FStar_Extraction_ML_Syntax.mlident)
  =
  fun g  ->
    fun l  ->
      fun t  ->
        fun t_x  ->
          fun add_unit  ->
            fun is_rec  ->
              match l with
              | FStar_Util.Inl x ->
                  let _0_183 = extend_bv g x t_x add_unit is_rec false  in
                  let _0_182 = bv_as_ml_termvar x  in (_0_183, _0_182)
              | FStar_Util.Inr f ->
                  let uu____893 =
                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                      (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                     in
                  (match uu____715 with
                   | (p,y) ->
                       let _0_184 = extend_fv' g f (p, y) t_x add_unit is_rec
                          in
                       (_0_184,
                         ((FStar_Extraction_ML_Syntax.avoid_keyword y),
                           (Prims.parse_int "0"))))
  
let extend_tydef :
  env -> FStar_Syntax_Syntax.fv -> FStar_Extraction_ML_Syntax.mltydecl -> env
  =
  fun g  ->
    fun fv  ->
      fun td  ->
        let m = module_name_of_fv fv  in
        let uu___106_740 = g  in
        {
          tcenv = (uu___109_916.tcenv);
          gamma = (uu___109_916.gamma);
          tydefs = ((m, td) :: (g.tydefs));
          currentModule = (uu___109_916.currentModule)
        }
  
let emptyMlPath :
  (FStar_Extraction_ML_Syntax.mlsymbol Prims.list * Prims.string) = ([], "") 
let mkContext : FStar_TypeChecker_Env.env -> env =
  fun e  ->
    let env =
      { tcenv = e; gamma = []; tydefs = []; currentModule = emptyMlPath }  in
    let a = ("'a", (~- (Prims.parse_int "1")))  in
    let failwith_ty =
      ([a],
        (FStar_Extraction_ML_Syntax.MLTY_Fun
           ((FStar_Extraction_ML_Syntax.MLTY_Named
               ([], (["Prims"], "string"))),
             FStar_Extraction_ML_Syntax.E_IMPURE,
             (FStar_Extraction_ML_Syntax.MLTY_Var a))))
       in
    let _0_186 =
      let _0_185 =
        FStar_Util.Inr
          (FStar_Syntax_Syntax.lid_as_fv FStar_Syntax_Const.failwith_lid
             FStar_Syntax_Syntax.Delta_constant None)
         in
      extend_lb env _0_185 FStar_Syntax_Syntax.tun failwith_ty false false
       in
    FStar_All.pipe_right _0_186 Prims.fst
  
let monad_op_name :
  FStar_Syntax_Syntax.eff_decl ->
    Prims.string -> (FStar_Extraction_ML_Syntax.mlpath * FStar_Ident.lident)
  =
  fun ed  ->
    fun nm  ->
      let uu____968 =
        (((ed.FStar_Syntax_Syntax.mname).FStar_Ident.ns),
          ((ed.FStar_Syntax_Syntax.mname).FStar_Ident.ident))
         in
      match uu____787 with
      | (module_name,eff_name) ->
          let mangled_name =
            Prims.strcat FStar_Ident.reserved_prefix
              (Prims.strcat eff_name.FStar_Ident.idText (Prims.strcat "_" nm))
             in
          let mangled_lid =
            FStar_Ident.lid_of_ids
              (FStar_List.append module_name
                 [FStar_Ident.id_of_text mangled_name])
             in
          let ml_name =
            FStar_Extraction_ML_Syntax.mlpath_of_lident mangled_lid  in
          let lid =
            FStar_All.pipe_right
              (FStar_List.append
                 (FStar_Ident.ids_of_lid ed.FStar_Syntax_Syntax.mname)
                 [FStar_Ident.id_of_text nm]) FStar_Ident.lid_of_ids
             in
          (ml_name, lid)
  
let action_name :
  FStar_Syntax_Syntax.eff_decl ->
    FStar_Syntax_Syntax.action ->
      (FStar_Extraction_ML_Syntax.mlpath * FStar_Ident.lident)
  =
  fun ed  ->
    fun a  ->
      monad_op_name ed
        ((a.FStar_Syntax_Syntax.action_name).FStar_Ident.ident).FStar_Ident.idText
  
let bind_name :
  FStar_Syntax_Syntax.eff_decl ->
    (FStar_Extraction_ML_Syntax.mlpath * FStar_Ident.lident)
  = fun ed  -> monad_op_name ed "bind" 
let return_name :
  FStar_Syntax_Syntax.eff_decl ->
    (FStar_Extraction_ML_Syntax.mlpath * FStar_Ident.lident)
  = fun ed  -> monad_op_name ed "return" 
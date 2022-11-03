open Prims
type changes = unit
type 't rwT = unit -> 't -> 't
let (rw_mlpath_ : FStar_Extraction_ML_Syntax.mlpath rwT) =
  fun changes1 ->
    fun uu___ ->
      match uu___ with
      | ("Foo"::[], "example") -> (["Superman"], "blurpon")
      | path -> path
let (rw_mlpath :
  unit ->
    FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlpath)
  = fun changes1 -> fun x -> rw_mlpath_ () x
let (rw_constant : FStar_Extraction_ML_Syntax.mlconstant rwT) =
  fun changes1 -> FStar_Pervasives.id
let (handle_projector :
  unit ->
    FStar_Extraction_ML_Syntax.mlexpr ->
      FStar_Extraction_ML_Syntax.mlpath -> FStar_Extraction_ML_Syntax.mlexpr')
  =
  fun x -> fun e -> fun path -> FStar_Extraction_ML_Syntax.MLE_Proj (e, path)
let rec (rw_ty : FStar_Extraction_ML_Syntax.mlty rwT) =
  fun changes1 ->
    fun uu___ ->
      match uu___ with
      | FStar_Extraction_ML_Syntax.MLTY_Fun (l, e, t) ->
          let uu___1 =
            let uu___2 = rw_ty () l in
            let uu___3 = rw_ty () t in (uu___2, e, uu___3) in
          FStar_Extraction_ML_Syntax.MLTY_Fun uu___1
      | FStar_Extraction_ML_Syntax.MLTY_Named (args, path) ->
          let uu___1 =
            let uu___2 = FStar_Compiler_List.map (rw_ty ()) args in
            let uu___3 = rw_mlpath () path in (uu___2, uu___3) in
          FStar_Extraction_ML_Syntax.MLTY_Named uu___1
      | FStar_Extraction_ML_Syntax.MLTY_Tuple args ->
          let uu___1 = FStar_Compiler_List.map (rw_ty ()) args in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu___1
      | ty -> ty
let rec (rw_expr : FStar_Extraction_ML_Syntax.mlexpr rwT) =
  fun changes1 ->
    fun e ->
      let uu___ = rw_expr' () e.FStar_Extraction_ML_Syntax.expr in
      let uu___1 = rw_ty () e.FStar_Extraction_ML_Syntax.mlty in
      {
        FStar_Extraction_ML_Syntax.expr = uu___;
        FStar_Extraction_ML_Syntax.mlty = uu___1;
        FStar_Extraction_ML_Syntax.loc = (e.FStar_Extraction_ML_Syntax.loc)
      }
and (rw_tyscheme : FStar_Extraction_ML_Syntax.mltyscheme rwT) =
  fun changes1 ->
    fun uu___ ->
      match uu___ with
      | (idents, ty) -> let uu___1 = rw_ty () ty in (idents, uu___1)
and (rw_lb : FStar_Extraction_ML_Syntax.mllb rwT) =
  fun changes1 ->
    fun lb ->
      let uu___ =
        FStar_Compiler_Util.map_opt lb.FStar_Extraction_ML_Syntax.mllb_tysc
          (rw_tyscheme ()) in
      let uu___1 = rw_expr () lb.FStar_Extraction_ML_Syntax.mllb_def in
      {
        FStar_Extraction_ML_Syntax.mllb_name =
          (lb.FStar_Extraction_ML_Syntax.mllb_name);
        FStar_Extraction_ML_Syntax.mllb_tysc = uu___;
        FStar_Extraction_ML_Syntax.mllb_add_unit =
          (lb.FStar_Extraction_ML_Syntax.mllb_add_unit);
        FStar_Extraction_ML_Syntax.mllb_def = uu___1;
        FStar_Extraction_ML_Syntax.mllb_meta =
          (lb.FStar_Extraction_ML_Syntax.mllb_meta);
        FStar_Extraction_ML_Syntax.print_typ =
          (lb.FStar_Extraction_ML_Syntax.print_typ)
      }
and (rw_letbinding : FStar_Extraction_ML_Syntax.mlletbinding rwT) =
  fun changes1 ->
    fun uu___ ->
      match uu___ with
      | (flavor, bindings) ->
          let uu___1 = FStar_Compiler_List.map (rw_lb ()) bindings in
          (flavor, uu___1)
and (rw_pattern : FStar_Extraction_ML_Syntax.mlpattern rwT) =
  fun changes1 ->
    fun uu___ ->
      match uu___ with
      | FStar_Extraction_ML_Syntax.MLP_Const c ->
          let uu___1 = rw_constant () c in
          FStar_Extraction_ML_Syntax.MLP_Const uu___1
      | FStar_Extraction_ML_Syntax.MLP_CTor (path, pats) ->
          let uu___1 =
            let uu___2 = rw_mlpath () path in
            let uu___3 = FStar_Compiler_List.map (rw_pattern ()) pats in
            (uu___2, uu___3) in
          FStar_Extraction_ML_Syntax.MLP_CTor uu___1
      | FStar_Extraction_ML_Syntax.MLP_Branch bs ->
          let uu___1 = FStar_Compiler_List.map (rw_pattern ()) bs in
          FStar_Extraction_ML_Syntax.MLP_Branch uu___1
      | FStar_Extraction_ML_Syntax.MLP_Record (s, pats) ->
          let uu___1 =
            let uu___2 =
              FStar_Compiler_List.map
                (fun uu___3 ->
                   match uu___3 with
                   | (s1, pat) ->
                       let uu___4 = rw_pattern () pat in (s1, uu___4)) pats in
            (s, uu___2) in
          FStar_Extraction_ML_Syntax.MLP_Record uu___1
      | FStar_Extraction_ML_Syntax.MLP_Tuple pats ->
          let uu___1 = FStar_Compiler_List.map (rw_pattern ()) pats in
          FStar_Extraction_ML_Syntax.MLP_Tuple uu___1
      | pat -> pat
and (rw_branch : FStar_Extraction_ML_Syntax.mlbranch rwT) =
  fun changes1 ->
    fun uu___ ->
      match uu___ with
      | (pat, e1, e2) ->
          let uu___1 = rw_pattern () pat in
          let uu___2 = FStar_Compiler_Util.map_opt e1 (rw_expr ()) in
          let uu___3 = rw_expr () e2 in (uu___1, uu___2, uu___3)
and (rw_expr' :
  unit ->
    FStar_Extraction_ML_Syntax.mlexpr' -> FStar_Extraction_ML_Syntax.mlexpr')
  =
  fun changes1 ->
    fun uu___ ->
      match uu___ with
      | FStar_Extraction_ML_Syntax.MLE_Name path ->
          let uu___1 = rw_mlpath () path in
          FStar_Extraction_ML_Syntax.MLE_Name uu___1
      | FStar_Extraction_ML_Syntax.MLE_Let (lb, e) ->
          let uu___1 =
            let uu___2 = rw_letbinding () lb in
            let uu___3 = rw_expr () e in (uu___2, uu___3) in
          FStar_Extraction_ML_Syntax.MLE_Let uu___1
      | FStar_Extraction_ML_Syntax.MLE_App (f, args) ->
          let uu___1 =
            let uu___2 = rw_expr () f in
            let uu___3 = FStar_Compiler_List.map (rw_expr ()) args in
            (uu___2, uu___3) in
          FStar_Extraction_ML_Syntax.MLE_App uu___1
      | FStar_Extraction_ML_Syntax.MLE_TApp (e, targs) ->
          let uu___1 =
            let uu___2 = rw_expr () e in
            let uu___3 = FStar_Compiler_List.map (rw_ty ()) targs in
            (uu___2, uu___3) in
          FStar_Extraction_ML_Syntax.MLE_TApp uu___1
      | FStar_Extraction_ML_Syntax.MLE_Fun (bds, body) ->
          let uu___1 =
            let uu___2 =
              FStar_Compiler_List.map
                (fun uu___3 ->
                   match uu___3 with
                   | (id, ty) -> let uu___4 = rw_ty () ty in (id, uu___4))
                bds in
            let uu___3 = rw_expr () body in (uu___2, uu___3) in
          FStar_Extraction_ML_Syntax.MLE_Fun uu___1
      | FStar_Extraction_ML_Syntax.MLE_Match (scrut, branches) ->
          let uu___1 =
            let uu___2 = rw_expr () scrut in
            let uu___3 = FStar_Compiler_List.map (rw_branch ()) branches in
            (uu___2, uu___3) in
          FStar_Extraction_ML_Syntax.MLE_Match uu___1
      | FStar_Extraction_ML_Syntax.MLE_Coerce (e, t1, t2) ->
          let uu___1 =
            let uu___2 = rw_expr () e in
            let uu___3 = rw_ty () t1 in
            let uu___4 = rw_ty () t2 in (uu___2, uu___3, uu___4) in
          FStar_Extraction_ML_Syntax.MLE_Coerce uu___1
      | FStar_Extraction_ML_Syntax.MLE_CTor (path, args) ->
          let uu___1 =
            let uu___2 = rw_mlpath () path in
            let uu___3 = FStar_Compiler_List.map (rw_expr ()) args in
            (uu___2, uu___3) in
          FStar_Extraction_ML_Syntax.MLE_CTor uu___1
      | FStar_Extraction_ML_Syntax.MLE_Seq args ->
          let uu___1 = FStar_Compiler_List.map (rw_expr ()) args in
          FStar_Extraction_ML_Syntax.MLE_Seq uu___1
      | FStar_Extraction_ML_Syntax.MLE_Tuple args ->
          let uu___1 = FStar_Compiler_List.map (rw_expr ()) args in
          FStar_Extraction_ML_Syntax.MLE_Tuple uu___1
      | FStar_Extraction_ML_Syntax.MLE_Record (symb, fields) ->
          let uu___1 =
            let uu___2 =
              FStar_Compiler_List.map
                (fun uu___3 ->
                   match uu___3 with
                   | (f, e) -> let uu___4 = rw_expr () e in (f, uu___4))
                fields in
            (symb, uu___2) in
          FStar_Extraction_ML_Syntax.MLE_Record uu___1
      | FStar_Extraction_ML_Syntax.MLE_Proj (e, path) ->
          let uu___1 = handle_projector () in uu___1 e path
      | FStar_Extraction_ML_Syntax.MLE_If (cond, then_, else_) ->
          let uu___1 =
            let uu___2 = rw_expr () cond in
            let uu___3 = rw_expr () then_ in
            let uu___4 = FStar_Compiler_Util.map_opt else_ (rw_expr ()) in
            (uu___2, uu___3, uu___4) in
          FStar_Extraction_ML_Syntax.MLE_If uu___1
      | FStar_Extraction_ML_Syntax.MLE_Raise (path, args) ->
          let uu___1 =
            let uu___2 = rw_mlpath () path in
            let uu___3 = FStar_Compiler_List.map (rw_expr ()) args in
            (uu___2, uu___3) in
          FStar_Extraction_ML_Syntax.MLE_Raise uu___1
      | FStar_Extraction_ML_Syntax.MLE_Try (e, branches) ->
          let uu___1 =
            let uu___2 = rw_expr () e in
            let uu___3 = FStar_Compiler_List.map (rw_branch ()) branches in
            (uu___2, uu___3) in
          FStar_Extraction_ML_Syntax.MLE_Try uu___1
      | FStar_Extraction_ML_Syntax.MLE_Const c ->
          let uu___1 = rw_constant () c in
          FStar_Extraction_ML_Syntax.MLE_Const uu___1
      | FStar_Extraction_ML_Syntax.MLE_Var i ->
          FStar_Extraction_ML_Syntax.MLE_Var i
let (rw_tybody : FStar_Extraction_ML_Syntax.mltybody rwT) =
  fun changes1 ->
    fun uu___ ->
      match uu___ with
      | FStar_Extraction_ML_Syntax.MLTD_Abbrev ty ->
          let uu___1 = rw_ty () ty in
          FStar_Extraction_ML_Syntax.MLTD_Abbrev uu___1
      | FStar_Extraction_ML_Syntax.MLTD_Record fields ->
          let uu___1 =
            FStar_Compiler_List.map
              (fun uu___2 ->
                 match uu___2 with
                 | (s, ty) -> let uu___3 = rw_ty () ty in (s, uu___3)) fields in
          FStar_Extraction_ML_Syntax.MLTD_Record uu___1
      | FStar_Extraction_ML_Syntax.MLTD_DType variants ->
          let uu___1 =
            FStar_Compiler_List.map
              (fun uu___2 ->
                 match uu___2 with
                 | (s, args) ->
                     let uu___3 =
                       FStar_Compiler_List.map
                         (fun uu___4 ->
                            match uu___4 with
                            | (s1, ty) ->
                                let uu___5 = rw_ty () ty in (s1, uu___5))
                         args in
                     (s, uu___3)) variants in
          FStar_Extraction_ML_Syntax.MLTD_DType uu___1
let (rw_onetydecl : FStar_Extraction_ML_Syntax.one_mltydecl rwT) =
  fun changes1 ->
    fun d ->
      let uu___ =
        FStar_Compiler_Util.map_opt d.FStar_Extraction_ML_Syntax.tydecl_defn
          (rw_tybody ()) in
      {
        FStar_Extraction_ML_Syntax.tydecl_assumed =
          (d.FStar_Extraction_ML_Syntax.tydecl_assumed);
        FStar_Extraction_ML_Syntax.tydecl_name =
          (d.FStar_Extraction_ML_Syntax.tydecl_name);
        FStar_Extraction_ML_Syntax.tydecl_ignored =
          (d.FStar_Extraction_ML_Syntax.tydecl_ignored);
        FStar_Extraction_ML_Syntax.tydecl_parameters =
          (d.FStar_Extraction_ML_Syntax.tydecl_parameters);
        FStar_Extraction_ML_Syntax.tydecl_meta =
          (d.FStar_Extraction_ML_Syntax.tydecl_meta);
        FStar_Extraction_ML_Syntax.tydecl_defn = uu___
      }
let (rw_tydecl : FStar_Extraction_ML_Syntax.mltydecl rwT) =
  fun changes1 -> FStar_Compiler_List.map (rw_onetydecl ())
let (rw_module1 : FStar_Extraction_ML_Syntax.mlmodule1 rwT) =
  fun changes1 ->
    fun uu___ ->
      match uu___ with
      | FStar_Extraction_ML_Syntax.MLM_Ty tydecl ->
          let uu___1 = rw_tydecl () tydecl in
          FStar_Extraction_ML_Syntax.MLM_Ty uu___1
      | FStar_Extraction_ML_Syntax.MLM_Let lb ->
          let uu___1 = rw_letbinding () lb in
          FStar_Extraction_ML_Syntax.MLM_Let uu___1
      | FStar_Extraction_ML_Syntax.MLM_Exn (s, args) ->
          let uu___1 =
            let uu___2 =
              FStar_Compiler_List.map
                (fun uu___3 ->
                   match uu___3 with
                   | (s1, ty) -> let uu___4 = rw_ty () ty in (s1, uu___4))
                args in
            (s, uu___2) in
          FStar_Extraction_ML_Syntax.MLM_Exn uu___1
      | FStar_Extraction_ML_Syntax.MLM_Top e ->
          let uu___1 = rw_expr () e in
          FStar_Extraction_ML_Syntax.MLM_Top uu___1
      | FStar_Extraction_ML_Syntax.MLM_Loc l ->
          FStar_Extraction_ML_Syntax.MLM_Loc l
let (rw_module : FStar_Extraction_ML_Syntax.mlmodule rwT) =
  fun changes1 -> FStar_Compiler_List.map (rw_module1 ())
let rec (rw_sig1 : FStar_Extraction_ML_Syntax.mlsig1 rwT) =
  fun changes1 ->
    fun uu___ ->
      match uu___ with
      | FStar_Extraction_ML_Syntax.MLS_Mod (s, sig1) ->
          let uu___1 = let uu___2 = rw_sig () sig1 in (s, uu___2) in
          FStar_Extraction_ML_Syntax.MLS_Mod uu___1
      | FStar_Extraction_ML_Syntax.MLS_Ty td ->
          let uu___1 = rw_tydecl () td in
          FStar_Extraction_ML_Syntax.MLS_Ty uu___1
      | FStar_Extraction_ML_Syntax.MLS_Val (s, tysch) ->
          let uu___1 = let uu___2 = rw_tyscheme () tysch in (s, uu___2) in
          FStar_Extraction_ML_Syntax.MLS_Val uu___1
      | FStar_Extraction_ML_Syntax.MLS_Exn (s, tys) ->
          let uu___1 =
            let uu___2 = FStar_Compiler_List.map (rw_ty ()) tys in
            (s, uu___2) in
          FStar_Extraction_ML_Syntax.MLS_Exn uu___1
and (rw_sig : FStar_Extraction_ML_Syntax.mlsig rwT) =
  fun changes1 -> FStar_Compiler_List.map (rw_sig1 ())
let rec (rw_mllib : FStar_Extraction_ML_Syntax.mllib rwT) =
  fun changes1 ->
    fun uu___ ->
      match uu___ with
      | FStar_Extraction_ML_Syntax.MLLib l ->
          let uu___1 =
            FStar_Compiler_List.map
              (fun uu___2 ->
                 match uu___2 with
                 | (path, opt, mllib) ->
                     let uu___3 = rw_mlpath () path in
                     let uu___4 =
                       FStar_Compiler_Util.map_opt opt
                         (fun uu___5 ->
                            match uu___5 with
                            | (sig1, mod1) ->
                                let uu___6 = rw_sig () sig1 in
                                let uu___7 = rw_module () mod1 in
                                (uu___6, uu___7)) in
                     let uu___5 = rw_mllib () mllib in
                     (uu___3, uu___4, uu___5)) l in
          FStar_Extraction_ML_Syntax.MLLib uu___1
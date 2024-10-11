open Prims
let (empty_defs : Pulse2Rust_Env.reachable_defs) =
  Obj.magic
    (FStarC_Class_Setlike.empty ()
       (Obj.magic
          (FStarC_Compiler_RBSet.setlike_rbset FStarC_Class_Ord.ord_string)) ())
let (singleton :
  FStarC_Extraction_ML_Syntax.mlpath -> Pulse2Rust_Env.reachable_defs) =
  fun uu___ ->
    (fun p ->
       let uu___ = FStarC_Extraction_ML_Syntax.string_of_mlpath p in
       Obj.magic
         (FStarC_Class_Setlike.singleton ()
            (Obj.magic
               (FStarC_Compiler_RBSet.setlike_rbset FStarC_Class_Ord.ord_string))
            uu___)) uu___
let reachable_defs_list :
  'a .
    ('a -> Pulse2Rust_Env.reachable_defs) ->
      'a Prims.list -> Pulse2Rust_Env.reachable_defs
  =
  fun f ->
    fun l ->
      let uu___ =
        Obj.magic
          (FStarC_Class_Setlike.empty ()
             (Obj.magic
                (FStarC_Compiler_RBSet.setlike_rbset
                   FStarC_Class_Ord.ord_string)) ()) in
      FStarC_Compiler_List.fold_left
        (fun uu___2 ->
           fun uu___1 ->
             (fun defs ->
                fun x ->
                  let uu___1 = f x in
                  Obj.magic
                    (FStarC_Class_Setlike.union ()
                       (Obj.magic
                          (FStarC_Compiler_RBSet.setlike_rbset
                             FStarC_Class_Ord.ord_string)) (Obj.magic defs)
                       (Obj.magic uu___1))) uu___2 uu___1) uu___ l
let reachable_defs_option :
  'a .
    ('a -> Pulse2Rust_Env.reachable_defs) ->
      'a FStar_Pervasives_Native.option -> Pulse2Rust_Env.reachable_defs
  =
  fun f ->
    fun o ->
      match o with
      | FStar_Pervasives_Native.None -> empty_defs
      | FStar_Pervasives_Native.Some x -> f x
let rec (reachable_defs_mlty :
  FStarC_Extraction_ML_Syntax.mlty -> Pulse2Rust_Env.reachable_defs) =
  fun uu___ ->
    (fun t ->
       match t with
       | FStarC_Extraction_ML_Syntax.MLTY_Var uu___ ->
           Obj.magic (Obj.repr empty_defs)
       | FStarC_Extraction_ML_Syntax.MLTY_Fun (t1, uu___, t2) ->
           Obj.magic
             (Obj.repr
                (let uu___1 = reachable_defs_mlty t1 in
                 let uu___2 = reachable_defs_mlty t2 in
                 FStarC_Class_Setlike.union ()
                   (Obj.magic
                      (FStarC_Compiler_RBSet.setlike_rbset
                         FStarC_Class_Ord.ord_string)) (Obj.magic uu___1)
                   (Obj.magic uu___2)))
       | FStarC_Extraction_ML_Syntax.MLTY_Named (tps, p) ->
           Obj.magic
             (Obj.repr
                (let uu___ = reachable_defs_list reachable_defs_mlty tps in
                 let uu___1 = singleton p in
                 FStarC_Class_Setlike.union ()
                   (Obj.magic
                      (FStarC_Compiler_RBSet.setlike_rbset
                         FStarC_Class_Ord.ord_string)) (Obj.magic uu___)
                   (Obj.magic uu___1)))
       | FStarC_Extraction_ML_Syntax.MLTY_Tuple ts ->
           Obj.magic (Obj.repr (reachable_defs_list reachable_defs_mlty ts))
       | FStarC_Extraction_ML_Syntax.MLTY_Top ->
           Obj.magic (Obj.repr empty_defs)
       | FStarC_Extraction_ML_Syntax.MLTY_Erased ->
           Obj.magic (Obj.repr empty_defs)) uu___
let (reachable_defs_mltyscheme :
  FStarC_Extraction_ML_Syntax.mltyscheme -> Pulse2Rust_Env.reachable_defs) =
  fun uu___ -> match uu___ with | (uu___1, t) -> reachable_defs_mlty t
let rec (reachable_defs_mlpattern :
  FStarC_Extraction_ML_Syntax.mlpattern -> Pulse2Rust_Env.reachable_defs) =
  fun uu___ ->
    (fun p ->
       match p with
       | FStarC_Extraction_ML_Syntax.MLP_Wild ->
           Obj.magic (Obj.repr empty_defs)
       | FStarC_Extraction_ML_Syntax.MLP_Const uu___ ->
           Obj.magic (Obj.repr empty_defs)
       | FStarC_Extraction_ML_Syntax.MLP_Var uu___ ->
           Obj.magic (Obj.repr empty_defs)
       | FStarC_Extraction_ML_Syntax.MLP_CTor (c, ps) ->
           Obj.magic
             (Obj.repr
                (let uu___ = singleton c in
                 let uu___1 = reachable_defs_list reachable_defs_mlpattern ps in
                 FStarC_Class_Setlike.union ()
                   (Obj.magic
                      (FStarC_Compiler_RBSet.setlike_rbset
                         FStarC_Class_Ord.ord_string)) (Obj.magic uu___)
                   (Obj.magic uu___1)))
       | FStarC_Extraction_ML_Syntax.MLP_Branch ps ->
           Obj.magic
             (Obj.repr (reachable_defs_list reachable_defs_mlpattern ps))
       | FStarC_Extraction_ML_Syntax.MLP_Record (syms, fs) ->
           Obj.magic
             (Obj.repr
                (let uu___ =
                   Obj.magic
                     (FStarC_Class_Setlike.singleton ()
                        (Obj.magic
                           (FStarC_Compiler_RBSet.setlike_rbset
                              FStarC_Class_Ord.ord_string))
                        (FStarC_Compiler_String.concat "." syms)) in
                 let uu___1 =
                   reachable_defs_list
                     (fun uu___2 ->
                        match uu___2 with
                        | (uu___3, p1) -> reachable_defs_mlpattern p1) fs in
                 FStarC_Class_Setlike.union ()
                   (Obj.magic
                      (FStarC_Compiler_RBSet.setlike_rbset
                         FStarC_Class_Ord.ord_string)) (Obj.magic uu___)
                   (Obj.magic uu___1)))
       | FStarC_Extraction_ML_Syntax.MLP_Tuple ps ->
           Obj.magic
             (Obj.repr (reachable_defs_list reachable_defs_mlpattern ps)))
      uu___
let rec (reachable_defs_expr' :
  FStarC_Extraction_ML_Syntax.mlexpr' -> Pulse2Rust_Env.reachable_defs) =
  fun uu___ ->
    (fun e ->
       match e with
       | FStarC_Extraction_ML_Syntax.MLE_Const uu___ ->
           Obj.magic (Obj.repr empty_defs)
       | FStarC_Extraction_ML_Syntax.MLE_Var uu___ ->
           Obj.magic (Obj.repr empty_defs)
       | FStarC_Extraction_ML_Syntax.MLE_Name p ->
           Obj.magic (Obj.repr (singleton p))
       | FStarC_Extraction_ML_Syntax.MLE_Let (lb, e1) ->
           Obj.magic
             (Obj.repr
                (let uu___ = reachable_defs_mlletbinding lb in
                 let uu___1 = reachable_defs_expr e1 in
                 FStarC_Class_Setlike.union ()
                   (Obj.magic
                      (FStarC_Compiler_RBSet.setlike_rbset
                         FStarC_Class_Ord.ord_string)) (Obj.magic uu___)
                   (Obj.magic uu___1)))
       | FStarC_Extraction_ML_Syntax.MLE_App (e1, es) ->
           Obj.magic
             (Obj.repr
                (let uu___ = reachable_defs_expr e1 in
                 let uu___1 = reachable_defs_list reachable_defs_expr es in
                 FStarC_Class_Setlike.union ()
                   (Obj.magic
                      (FStarC_Compiler_RBSet.setlike_rbset
                         FStarC_Class_Ord.ord_string)) (Obj.magic uu___)
                   (Obj.magic uu___1)))
       | FStarC_Extraction_ML_Syntax.MLE_TApp (e1, ts) ->
           Obj.magic
             (Obj.repr
                (let uu___ = reachable_defs_expr e1 in
                 let uu___1 = reachable_defs_list reachable_defs_mlty ts in
                 FStarC_Class_Setlike.union ()
                   (Obj.magic
                      (FStarC_Compiler_RBSet.setlike_rbset
                         FStarC_Class_Ord.ord_string)) (Obj.magic uu___)
                   (Obj.magic uu___1)))
       | FStarC_Extraction_ML_Syntax.MLE_Fun (args, e1) ->
           Obj.magic
             (Obj.repr
                (let uu___ =
                   reachable_defs_list
                     (fun b ->
                        reachable_defs_mlty
                          b.FStarC_Extraction_ML_Syntax.mlbinder_ty) args in
                 let uu___1 = reachable_defs_expr e1 in
                 FStarC_Class_Setlike.union ()
                   (Obj.magic
                      (FStarC_Compiler_RBSet.setlike_rbset
                         FStarC_Class_Ord.ord_string)) (Obj.magic uu___)
                   (Obj.magic uu___1)))
       | FStarC_Extraction_ML_Syntax.MLE_Match (e1, bs) ->
           Obj.magic
             (Obj.repr
                (let uu___ = reachable_defs_expr e1 in
                 let uu___1 = reachable_defs_list reachable_defs_mlbranch bs in
                 FStarC_Class_Setlike.union ()
                   (Obj.magic
                      (FStarC_Compiler_RBSet.setlike_rbset
                         FStarC_Class_Ord.ord_string)) (Obj.magic uu___)
                   (Obj.magic uu___1)))
       | FStarC_Extraction_ML_Syntax.MLE_Coerce (e1, t1, t2) ->
           Obj.magic
             (Obj.repr
                (let uu___ = reachable_defs_expr e1 in
                 let uu___1 =
                   let uu___2 = reachable_defs_mlty t1 in
                   let uu___3 = reachable_defs_mlty t2 in
                   Obj.magic
                     (FStarC_Class_Setlike.union ()
                        (Obj.magic
                           (FStarC_Compiler_RBSet.setlike_rbset
                              FStarC_Class_Ord.ord_string)) (Obj.magic uu___2)
                        (Obj.magic uu___3)) in
                 FStarC_Class_Setlike.union ()
                   (Obj.magic
                      (FStarC_Compiler_RBSet.setlike_rbset
                         FStarC_Class_Ord.ord_string)) (Obj.magic uu___)
                   (Obj.magic uu___1)))
       | FStarC_Extraction_ML_Syntax.MLE_CTor (p, es) ->
           Obj.magic
             (Obj.repr
                (let uu___ = singleton p in
                 let uu___1 = reachable_defs_list reachable_defs_expr es in
                 FStarC_Class_Setlike.union ()
                   (Obj.magic
                      (FStarC_Compiler_RBSet.setlike_rbset
                         FStarC_Class_Ord.ord_string)) (Obj.magic uu___)
                   (Obj.magic uu___1)))
       | FStarC_Extraction_ML_Syntax.MLE_Seq es ->
           Obj.magic (Obj.repr (reachable_defs_list reachable_defs_expr es))
       | FStarC_Extraction_ML_Syntax.MLE_Tuple es ->
           Obj.magic (Obj.repr (reachable_defs_list reachable_defs_expr es))
       | FStarC_Extraction_ML_Syntax.MLE_Record (p, n, fs) ->
           Obj.magic
             (Obj.repr
                (let uu___ =
                   Obj.magic
                     (FStarC_Class_Setlike.singleton ()
                        (Obj.magic
                           (FStarC_Compiler_RBSet.setlike_rbset
                              FStarC_Class_Ord.ord_string))
                        (FStarC_Compiler_String.concat "."
                           (FStarC_Compiler_List.op_At p [n]))) in
                 let uu___1 =
                   reachable_defs_list
                     (fun uu___2 ->
                        match uu___2 with
                        | (uu___3, e1) -> reachable_defs_expr e1) fs in
                 FStarC_Class_Setlike.union ()
                   (Obj.magic
                      (FStarC_Compiler_RBSet.setlike_rbset
                         FStarC_Class_Ord.ord_string)) (Obj.magic uu___)
                   (Obj.magic uu___1)))
       | FStarC_Extraction_ML_Syntax.MLE_Proj (e1, uu___) ->
           Obj.magic (Obj.repr (reachable_defs_expr e1))
       | FStarC_Extraction_ML_Syntax.MLE_If (e1, e2, e3_opt) ->
           Obj.magic
             (Obj.repr
                (let uu___ = reachable_defs_expr e1 in
                 let uu___1 =
                   let uu___2 = reachable_defs_expr e2 in
                   let uu___3 =
                     reachable_defs_option reachable_defs_expr e3_opt in
                   Obj.magic
                     (FStarC_Class_Setlike.union ()
                        (Obj.magic
                           (FStarC_Compiler_RBSet.setlike_rbset
                              FStarC_Class_Ord.ord_string)) (Obj.magic uu___2)
                        (Obj.magic uu___3)) in
                 FStarC_Class_Setlike.union ()
                   (Obj.magic
                      (FStarC_Compiler_RBSet.setlike_rbset
                         FStarC_Class_Ord.ord_string)) (Obj.magic uu___)
                   (Obj.magic uu___1)))
       | FStarC_Extraction_ML_Syntax.MLE_Raise (p, es) ->
           Obj.magic
             (Obj.repr
                (let uu___ = singleton p in
                 let uu___1 = reachable_defs_list reachable_defs_expr es in
                 FStarC_Class_Setlike.union ()
                   (Obj.magic
                      (FStarC_Compiler_RBSet.setlike_rbset
                         FStarC_Class_Ord.ord_string)) (Obj.magic uu___)
                   (Obj.magic uu___1)))
       | FStarC_Extraction_ML_Syntax.MLE_Try (e1, bs) ->
           Obj.magic
             (Obj.repr
                (let uu___ = reachable_defs_expr e1 in
                 let uu___1 = reachable_defs_list reachable_defs_mlbranch bs in
                 FStarC_Class_Setlike.union ()
                   (Obj.magic
                      (FStarC_Compiler_RBSet.setlike_rbset
                         FStarC_Class_Ord.ord_string)) (Obj.magic uu___)
                   (Obj.magic uu___1)))) uu___
and (reachable_defs_expr :
  FStarC_Extraction_ML_Syntax.mlexpr -> Pulse2Rust_Env.reachable_defs) =
  fun uu___ ->
    (fun e ->
       let uu___ = reachable_defs_expr' e.FStarC_Extraction_ML_Syntax.expr in
       let uu___1 = reachable_defs_mlty e.FStarC_Extraction_ML_Syntax.mlty in
       Obj.magic
         (FStarC_Class_Setlike.union ()
            (Obj.magic
               (FStarC_Compiler_RBSet.setlike_rbset FStarC_Class_Ord.ord_string))
            (Obj.magic uu___) (Obj.magic uu___1))) uu___
and (reachable_defs_mlbranch :
  FStarC_Extraction_ML_Syntax.mlbranch -> Pulse2Rust_Env.reachable_defs) =
  fun uu___ ->
    (fun uu___ ->
       match uu___ with
       | (p, wopt, e) ->
           let uu___1 = reachable_defs_mlpattern p in
           let uu___2 =
             let uu___3 = reachable_defs_option reachable_defs_expr wopt in
             let uu___4 = reachable_defs_expr e in
             Obj.magic
               (FStarC_Class_Setlike.union ()
                  (Obj.magic
                     (FStarC_Compiler_RBSet.setlike_rbset
                        FStarC_Class_Ord.ord_string)) (Obj.magic uu___3)
                  (Obj.magic uu___4)) in
           Obj.magic
             (FStarC_Class_Setlike.union ()
                (Obj.magic
                   (FStarC_Compiler_RBSet.setlike_rbset
                      FStarC_Class_Ord.ord_string)) (Obj.magic uu___1)
                (Obj.magic uu___2))) uu___
and (reachable_defs_mllb :
  FStarC_Extraction_ML_Syntax.mllb -> Pulse2Rust_Env.reachable_defs) =
  fun uu___ ->
    (fun lb ->
       let uu___ =
         reachable_defs_option reachable_defs_mltyscheme
           lb.FStarC_Extraction_ML_Syntax.mllb_tysc in
       let uu___1 =
         reachable_defs_expr lb.FStarC_Extraction_ML_Syntax.mllb_def in
       Obj.magic
         (FStarC_Class_Setlike.union ()
            (Obj.magic
               (FStarC_Compiler_RBSet.setlike_rbset FStarC_Class_Ord.ord_string))
            (Obj.magic uu___) (Obj.magic uu___1))) uu___
and (reachable_defs_mlletbinding :
  FStarC_Extraction_ML_Syntax.mlletbinding -> Pulse2Rust_Env.reachable_defs) =
  fun uu___ ->
    match uu___ with
    | (uu___1, lbs) -> reachable_defs_list reachable_defs_mllb lbs
let (reachable_defs_mltybody :
  FStarC_Extraction_ML_Syntax.mltybody -> Pulse2Rust_Env.reachable_defs) =
  fun t ->
    match t with
    | FStarC_Extraction_ML_Syntax.MLTD_Abbrev t1 -> reachable_defs_mlty t1
    | FStarC_Extraction_ML_Syntax.MLTD_Record fs ->
        reachable_defs_list
          (fun uu___ ->
             match uu___ with | (uu___1, t1) -> reachable_defs_mlty t1) fs
    | FStarC_Extraction_ML_Syntax.MLTD_DType cts ->
        reachable_defs_list
          (fun uu___ ->
             match uu___ with
             | (uu___1, dts) ->
                 reachable_defs_list
                   (fun uu___2 ->
                      match uu___2 with
                      | (uu___3, t1) -> reachable_defs_mlty t1) dts) cts
let (reachable_defs_one_mltydecl :
  FStarC_Extraction_ML_Syntax.one_mltydecl -> Pulse2Rust_Env.reachable_defs) =
  fun t ->
    reachable_defs_option reachable_defs_mltybody
      t.FStarC_Extraction_ML_Syntax.tydecl_defn
let (reachable_defs_mltydecl :
  FStarC_Extraction_ML_Syntax.mltydecl -> Pulse2Rust_Env.reachable_defs) =
  fun t -> reachable_defs_list reachable_defs_one_mltydecl t
let (reachable_defs_mlmodule1 :
  FStarC_Extraction_ML_Syntax.mlmodule1 -> Pulse2Rust_Env.reachable_defs) =
  fun m ->
    let defs =
      match m.FStarC_Extraction_ML_Syntax.mlmodule1_m with
      | FStarC_Extraction_ML_Syntax.MLM_Ty t -> reachable_defs_mltydecl t
      | FStarC_Extraction_ML_Syntax.MLM_Let lb ->
          reachable_defs_mlletbinding lb
      | FStarC_Extraction_ML_Syntax.MLM_Exn (uu___, args) ->
          reachable_defs_list
            (fun uu___1 ->
               match uu___1 with | (uu___2, t) -> reachable_defs_mlty t) args
      | FStarC_Extraction_ML_Syntax.MLM_Top e -> reachable_defs_expr e
      | FStarC_Extraction_ML_Syntax.MLM_Loc uu___ -> empty_defs in
    defs
let (reachable_defs_decls :
  FStarC_Extraction_ML_Syntax.mlmodule -> Pulse2Rust_Env.reachable_defs) =
  fun decls -> reachable_defs_list reachable_defs_mlmodule1 decls
let (decl_reachable :
  Pulse2Rust_Env.reachable_defs ->
    Prims.string -> FStarC_Extraction_ML_Syntax.mlmodule1 -> Prims.bool)
  =
  fun reachable_defs ->
    fun mname ->
      fun d ->
        match d.FStarC_Extraction_ML_Syntax.mlmodule1_m with
        | FStarC_Extraction_ML_Syntax.MLM_Ty t ->
            FStarC_Compiler_List.existsb
              (fun ty_decl ->
                 FStarC_Class_Setlike.mem ()
                   (Obj.magic
                      (FStarC_Compiler_RBSet.setlike_rbset
                         FStarC_Class_Ord.ord_string))
                   (Prims.strcat mname
                      (Prims.strcat "."
                         ty_decl.FStarC_Extraction_ML_Syntax.tydecl_name))
                   (Obj.magic reachable_defs)) t
        | FStarC_Extraction_ML_Syntax.MLM_Let (uu___, lbs) ->
            FStarC_Compiler_List.existsb
              (fun lb ->
                 FStarC_Class_Setlike.mem ()
                   (Obj.magic
                      (FStarC_Compiler_RBSet.setlike_rbset
                         FStarC_Class_Ord.ord_string))
                   (Prims.strcat mname
                      (Prims.strcat "."
                         lb.FStarC_Extraction_ML_Syntax.mllb_name))
                   (Obj.magic reachable_defs)) lbs
        | FStarC_Extraction_ML_Syntax.MLM_Exn (p, uu___) -> false
        | FStarC_Extraction_ML_Syntax.MLM_Top uu___ -> false
        | FStarC_Extraction_ML_Syntax.MLM_Loc uu___ -> false
let rec (topsort :
  Pulse2Rust_Env.dict ->
    Prims.string Prims.list ->
      Prims.string Prims.list ->
        Prims.string -> (Prims.string Prims.list * Prims.string Prims.list))
  =
  fun d ->
    fun grey ->
      fun black ->
        fun root ->
          let grey1 = root :: grey in
          let deps =
            let uu___ =
              let uu___1 = FStarC_Compiler_Util.smap_try_find d root in
              FStarC_Compiler_Util.must uu___1 in
            match uu___ with | (deps1, uu___1, uu___2) -> deps1 in
          let deps1 =
            FStarC_Compiler_List.filter
              (fun f ->
                 (let uu___ = FStarC_Compiler_Util.smap_keys d in
                  FStarC_Compiler_List.mem f uu___) &&
                   (Prims.op_Negation (f = root))) deps in
          (let uu___1 =
             FStarC_Compiler_List.existsb
               (fun d1 -> FStarC_Compiler_List.mem d1 grey1) deps1 in
           if uu___1
           then
             let uu___2 =
               FStarC_Compiler_Util.format1 "cyclic dependency: %s" root in
             FStarC_Compiler_Effect.failwith uu___2
           else ());
          (let deps2 =
             FStarC_Compiler_List.filter
               (fun f -> Prims.op_Negation (FStarC_Compiler_List.mem f black))
               deps1 in
           let uu___1 =
             FStarC_Compiler_List.fold_left
               (fun uu___2 ->
                  fun dep ->
                    match uu___2 with
                    | (grey2, black1) -> topsort d grey2 black1 dep)
               (grey1, black) deps2 in
           match uu___1 with
           | (grey2, black1) ->
               let uu___2 =
                 FStarC_Compiler_List.filter
                   (fun g -> Prims.op_Negation (g = root)) grey2 in
               (uu___2,
                 (if FStarC_Compiler_List.mem root black1
                  then black1
                  else root :: black1)))
let rec (topsort_all :
  Pulse2Rust_Env.dict -> Prims.string Prims.list -> Prims.string Prims.list)
  =
  fun d ->
    fun black ->
      let uu___ =
        let uu___1 = FStarC_Compiler_Util.smap_keys d in
        FStarC_Compiler_List.for_all
          (fun f -> FStarC_Compiler_List.contains f black) uu___1 in
      if uu___
      then black
      else
        (let rem =
           let uu___2 = FStarC_Compiler_Util.smap_keys d in
           FStarC_Compiler_List.filter
             (fun f ->
                Prims.op_Negation (FStarC_Compiler_List.contains f black))
             uu___2 in
         let root =
           FStarC_Compiler_List.nth rem
             ((FStarC_Compiler_List.length rem) - Prims.int_one) in
         let uu___2 = topsort d [] black root in
         match uu___2 with
         | (grey, black1) ->
             (if (FStarC_Compiler_List.length grey) <> Prims.int_zero
              then
                FStarC_Compiler_Effect.failwith
                  "topsort_all: not all files are reachable"
              else ();
              topsort_all d black1))
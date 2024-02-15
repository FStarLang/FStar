open Prims
let (empty_defs : Pulse2Rust_Env.reachable_defs) =
  FStar_Compiler_Set.empty FStar_Class_Ord.ord_string ()
let (singleton :
  FStar_Extraction_ML_Syntax.mlpath -> Pulse2Rust_Env.reachable_defs) =
  fun p ->
    let uu___ = FStar_Extraction_ML_Syntax.string_of_mlpath p in
    FStar_Compiler_Set.singleton FStar_Class_Ord.ord_string uu___
let reachable_defs_list :
  'a .
    ('a -> Pulse2Rust_Env.reachable_defs) ->
      'a Prims.list -> Pulse2Rust_Env.reachable_defs
  =
  fun f ->
    fun l ->
      let uu___ = FStar_Compiler_Set.empty FStar_Class_Ord.ord_string () in
      FStar_Compiler_List.fold_left
        (fun defs ->
           fun x ->
             let uu___1 = f x in
             FStar_Compiler_Set.union FStar_Class_Ord.ord_string defs uu___1)
        uu___ l
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
  FStar_Extraction_ML_Syntax.mlty -> Pulse2Rust_Env.reachable_defs) =
  fun t ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Var uu___ -> empty_defs
    | FStar_Extraction_ML_Syntax.MLTY_Fun (t1, uu___, t2) ->
        let uu___1 = reachable_defs_mlty t1 in
        let uu___2 = reachable_defs_mlty t2 in
        FStar_Compiler_Set.union FStar_Class_Ord.ord_string uu___1 uu___2
    | FStar_Extraction_ML_Syntax.MLTY_Named (tps, p) ->
        let uu___ = reachable_defs_list reachable_defs_mlty tps in
        let uu___1 = singleton p in
        FStar_Compiler_Set.union FStar_Class_Ord.ord_string uu___ uu___1
    | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
        reachable_defs_list reachable_defs_mlty ts
    | FStar_Extraction_ML_Syntax.MLTY_Top -> empty_defs
    | FStar_Extraction_ML_Syntax.MLTY_Erased -> empty_defs
let (reachable_defs_mltyscheme :
  FStar_Extraction_ML_Syntax.mltyscheme -> Pulse2Rust_Env.reachable_defs) =
  fun uu___ -> match uu___ with | (uu___1, t) -> reachable_defs_mlty t
let rec (reachable_defs_mlpattern :
  FStar_Extraction_ML_Syntax.mlpattern -> Pulse2Rust_Env.reachable_defs) =
  fun p ->
    match p with
    | FStar_Extraction_ML_Syntax.MLP_Wild -> empty_defs
    | FStar_Extraction_ML_Syntax.MLP_Const uu___ -> empty_defs
    | FStar_Extraction_ML_Syntax.MLP_Var uu___ -> empty_defs
    | FStar_Extraction_ML_Syntax.MLP_CTor (c, ps) ->
        let uu___ = singleton c in
        let uu___1 = reachable_defs_list reachable_defs_mlpattern ps in
        FStar_Compiler_Set.union FStar_Class_Ord.ord_string uu___ uu___1
    | FStar_Extraction_ML_Syntax.MLP_Branch ps ->
        reachable_defs_list reachable_defs_mlpattern ps
    | FStar_Extraction_ML_Syntax.MLP_Record (syms, fs) ->
        let uu___ =
          FStar_Compiler_Set.singleton FStar_Class_Ord.ord_string
            (FStar_Compiler_String.concat "." syms) in
        let uu___1 =
          reachable_defs_list
            (fun uu___2 ->
               match uu___2 with
               | (uu___3, p1) -> reachable_defs_mlpattern p1) fs in
        FStar_Compiler_Set.union FStar_Class_Ord.ord_string uu___ uu___1
    | FStar_Extraction_ML_Syntax.MLP_Tuple ps ->
        reachable_defs_list reachable_defs_mlpattern ps
let rec (reachable_defs_expr' :
  FStar_Extraction_ML_Syntax.mlexpr' -> Pulse2Rust_Env.reachable_defs) =
  fun e ->
    match e with
    | FStar_Extraction_ML_Syntax.MLE_Const uu___ -> empty_defs
    | FStar_Extraction_ML_Syntax.MLE_Var uu___ -> empty_defs
    | FStar_Extraction_ML_Syntax.MLE_Name p -> singleton p
    | FStar_Extraction_ML_Syntax.MLE_Let (lb, e1) ->
        let uu___ = reachable_defs_mlletbinding lb in
        let uu___1 = reachable_defs_expr e1 in
        FStar_Compiler_Set.union FStar_Class_Ord.ord_string uu___ uu___1
    | FStar_Extraction_ML_Syntax.MLE_App (e1, es) ->
        let uu___ = reachable_defs_expr e1 in
        let uu___1 = reachable_defs_list reachable_defs_expr es in
        FStar_Compiler_Set.union FStar_Class_Ord.ord_string uu___ uu___1
    | FStar_Extraction_ML_Syntax.MLE_TApp (e1, ts) ->
        let uu___ = reachable_defs_expr e1 in
        let uu___1 = reachable_defs_list reachable_defs_mlty ts in
        FStar_Compiler_Set.union FStar_Class_Ord.ord_string uu___ uu___1
    | FStar_Extraction_ML_Syntax.MLE_Fun (args, e1) ->
        let uu___ =
          reachable_defs_list
            (fun b ->
               reachable_defs_mlty b.FStar_Extraction_ML_Syntax.mlbinder_ty)
            args in
        let uu___1 = reachable_defs_expr e1 in
        FStar_Compiler_Set.union FStar_Class_Ord.ord_string uu___ uu___1
    | FStar_Extraction_ML_Syntax.MLE_Match (e1, bs) ->
        let uu___ = reachable_defs_expr e1 in
        let uu___1 = reachable_defs_list reachable_defs_mlbranch bs in
        FStar_Compiler_Set.union FStar_Class_Ord.ord_string uu___ uu___1
    | FStar_Extraction_ML_Syntax.MLE_Coerce (e1, t1, t2) ->
        let uu___ = reachable_defs_expr e1 in
        let uu___1 =
          let uu___2 = reachable_defs_mlty t1 in
          let uu___3 = reachable_defs_mlty t2 in
          FStar_Compiler_Set.union FStar_Class_Ord.ord_string uu___2 uu___3 in
        FStar_Compiler_Set.union FStar_Class_Ord.ord_string uu___ uu___1
    | FStar_Extraction_ML_Syntax.MLE_CTor (p, es) ->
        let uu___ = singleton p in
        let uu___1 = reachable_defs_list reachable_defs_expr es in
        FStar_Compiler_Set.union FStar_Class_Ord.ord_string uu___ uu___1
    | FStar_Extraction_ML_Syntax.MLE_Seq es ->
        reachable_defs_list reachable_defs_expr es
    | FStar_Extraction_ML_Syntax.MLE_Tuple es ->
        reachable_defs_list reachable_defs_expr es
    | FStar_Extraction_ML_Syntax.MLE_Record (p, n, fs) ->
        let uu___ =
          FStar_Compiler_Set.singleton FStar_Class_Ord.ord_string
            (FStar_Compiler_String.concat "."
               (FStar_Compiler_List.op_At p [n])) in
        let uu___1 =
          reachable_defs_list
            (fun uu___2 ->
               match uu___2 with | (uu___3, e1) -> reachable_defs_expr e1) fs in
        FStar_Compiler_Set.union FStar_Class_Ord.ord_string uu___ uu___1
    | FStar_Extraction_ML_Syntax.MLE_Proj (e1, uu___) ->
        reachable_defs_expr e1
    | FStar_Extraction_ML_Syntax.MLE_If (e1, e2, e3_opt) ->
        let uu___ = reachable_defs_expr e1 in
        let uu___1 =
          let uu___2 = reachable_defs_expr e2 in
          let uu___3 = reachable_defs_option reachable_defs_expr e3_opt in
          FStar_Compiler_Set.union FStar_Class_Ord.ord_string uu___2 uu___3 in
        FStar_Compiler_Set.union FStar_Class_Ord.ord_string uu___ uu___1
    | FStar_Extraction_ML_Syntax.MLE_Raise (p, es) ->
        let uu___ = singleton p in
        let uu___1 = reachable_defs_list reachable_defs_expr es in
        FStar_Compiler_Set.union FStar_Class_Ord.ord_string uu___ uu___1
    | FStar_Extraction_ML_Syntax.MLE_Try (e1, bs) ->
        let uu___ = reachable_defs_expr e1 in
        let uu___1 = reachable_defs_list reachable_defs_mlbranch bs in
        FStar_Compiler_Set.union FStar_Class_Ord.ord_string uu___ uu___1
and (reachable_defs_expr :
  FStar_Extraction_ML_Syntax.mlexpr -> Pulse2Rust_Env.reachable_defs) =
  fun e ->
    let uu___ = reachable_defs_expr' e.FStar_Extraction_ML_Syntax.expr in
    let uu___1 = reachable_defs_mlty e.FStar_Extraction_ML_Syntax.mlty in
    FStar_Compiler_Set.union FStar_Class_Ord.ord_string uu___ uu___1
and (reachable_defs_mlbranch :
  FStar_Extraction_ML_Syntax.mlbranch -> Pulse2Rust_Env.reachable_defs) =
  fun uu___ ->
    match uu___ with
    | (p, wopt, e) ->
        let uu___1 = reachable_defs_mlpattern p in
        let uu___2 =
          let uu___3 = reachable_defs_option reachable_defs_expr wopt in
          let uu___4 = reachable_defs_expr e in
          FStar_Compiler_Set.union FStar_Class_Ord.ord_string uu___3 uu___4 in
        FStar_Compiler_Set.union FStar_Class_Ord.ord_string uu___1 uu___2
and (reachable_defs_mllb :
  FStar_Extraction_ML_Syntax.mllb -> Pulse2Rust_Env.reachable_defs) =
  fun lb ->
    let uu___ =
      reachable_defs_option reachable_defs_mltyscheme
        lb.FStar_Extraction_ML_Syntax.mllb_tysc in
    let uu___1 = reachable_defs_expr lb.FStar_Extraction_ML_Syntax.mllb_def in
    FStar_Compiler_Set.union FStar_Class_Ord.ord_string uu___ uu___1
and (reachable_defs_mlletbinding :
  FStar_Extraction_ML_Syntax.mlletbinding -> Pulse2Rust_Env.reachable_defs) =
  fun uu___ ->
    match uu___ with
    | (uu___1, lbs) -> reachable_defs_list reachable_defs_mllb lbs
let (reachable_defs_mltybody :
  FStar_Extraction_ML_Syntax.mltybody -> Pulse2Rust_Env.reachable_defs) =
  fun t ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTD_Abbrev t1 -> reachable_defs_mlty t1
    | FStar_Extraction_ML_Syntax.MLTD_Record fs ->
        reachable_defs_list
          (fun uu___ ->
             match uu___ with | (uu___1, t1) -> reachable_defs_mlty t1) fs
    | FStar_Extraction_ML_Syntax.MLTD_DType cts ->
        reachable_defs_list
          (fun uu___ ->
             match uu___ with
             | (uu___1, dts) ->
                 reachable_defs_list
                   (fun uu___2 ->
                      match uu___2 with
                      | (uu___3, t1) -> reachable_defs_mlty t1) dts) cts
let (reachable_defs_one_mltydecl :
  FStar_Extraction_ML_Syntax.one_mltydecl -> Pulse2Rust_Env.reachable_defs) =
  fun t ->
    reachable_defs_option reachable_defs_mltybody
      t.FStar_Extraction_ML_Syntax.tydecl_defn
let (reachable_defs_mltydecl :
  FStar_Extraction_ML_Syntax.mltydecl -> Pulse2Rust_Env.reachable_defs) =
  fun t -> reachable_defs_list reachable_defs_one_mltydecl t
let (reachable_defs_mlmodule1 :
  FStar_Extraction_ML_Syntax.mlmodule1 -> Pulse2Rust_Env.reachable_defs) =
  fun m ->
    let defs =
      match m.FStar_Extraction_ML_Syntax.mlmodule1_m with
      | FStar_Extraction_ML_Syntax.MLM_Ty t -> reachable_defs_mltydecl t
      | FStar_Extraction_ML_Syntax.MLM_Let lb ->
          reachable_defs_mlletbinding lb
      | FStar_Extraction_ML_Syntax.MLM_Exn (uu___, args) ->
          reachable_defs_list
            (fun uu___1 ->
               match uu___1 with | (uu___2, t) -> reachable_defs_mlty t) args
      | FStar_Extraction_ML_Syntax.MLM_Top e -> reachable_defs_expr e
      | FStar_Extraction_ML_Syntax.MLM_Loc uu___ -> empty_defs in
    defs
let (reachable_defs_decls :
  FStar_Extraction_ML_Syntax.mlmodule -> Pulse2Rust_Env.reachable_defs) =
  fun decls -> reachable_defs_list reachable_defs_mlmodule1 decls
let (decl_reachable :
  Pulse2Rust_Env.reachable_defs ->
    Prims.string -> FStar_Extraction_ML_Syntax.mlmodule1 -> Prims.bool)
  =
  fun reachable_defs ->
    fun mname ->
      fun d ->
        match d.FStar_Extraction_ML_Syntax.mlmodule1_m with
        | FStar_Extraction_ML_Syntax.MLM_Ty t ->
            FStar_Compiler_List.existsb
              (fun ty_decl ->
                 FStar_Compiler_Set.mem FStar_Class_Ord.ord_string
                   (Prims.strcat mname
                      (Prims.strcat "."
                         ty_decl.FStar_Extraction_ML_Syntax.tydecl_name))
                   reachable_defs) t
        | FStar_Extraction_ML_Syntax.MLM_Let (uu___, lbs) ->
            FStar_Compiler_List.existsb
              (fun lb ->
                 FStar_Compiler_Set.mem FStar_Class_Ord.ord_string
                   (Prims.strcat mname
                      (Prims.strcat "."
                         lb.FStar_Extraction_ML_Syntax.mllb_name))
                   reachable_defs) lbs
        | FStar_Extraction_ML_Syntax.MLM_Exn (p, uu___) -> false
        | FStar_Extraction_ML_Syntax.MLM_Top uu___ -> false
        | FStar_Extraction_ML_Syntax.MLM_Loc uu___ -> false
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
              let uu___1 = FStar_Compiler_Util.smap_try_find d root in
              FStar_Compiler_Util.must uu___1 in
            match uu___ with | (deps1, uu___1, uu___2) -> deps1 in
          let deps1 =
            FStar_Compiler_List.filter
              (fun f ->
                 (let uu___ = FStar_Compiler_Util.smap_keys d in
                  FStar_Compiler_List.mem f uu___) &&
                   (Prims.op_Negation (f = root))) deps in
          (let uu___1 =
             FStar_Compiler_List.existsb
               (fun d1 -> FStar_Compiler_List.mem d1 grey1) deps1 in
           if uu___1
           then
             let uu___2 =
               FStar_Compiler_Util.format1 "cyclic dependency: %s" root in
             FStar_Compiler_Effect.failwith uu___2
           else ());
          (let deps2 =
             FStar_Compiler_List.filter
               (fun f -> Prims.op_Negation (FStar_Compiler_List.mem f black))
               deps1 in
           let uu___1 =
             FStar_Compiler_List.fold_left
               (fun uu___2 ->
                  fun dep ->
                    match uu___2 with
                    | (grey2, black1) -> topsort d grey2 black1 dep)
               (grey1, black) deps2 in
           match uu___1 with
           | (grey2, black1) ->
               let uu___2 =
                 FStar_Compiler_List.filter
                   (fun g -> Prims.op_Negation (g = root)) grey2 in
               (uu___2,
                 (if FStar_Compiler_List.mem root black1
                  then black1
                  else root :: black1)))
let rec (topsort_all :
  Pulse2Rust_Env.dict -> Prims.string Prims.list -> Prims.string Prims.list)
  =
  fun d ->
    fun black ->
      let uu___ =
        let uu___1 = FStar_Compiler_Util.smap_keys d in
        FStar_Compiler_List.for_all
          (fun f -> FStar_Compiler_List.contains f black) uu___1 in
      if uu___
      then black
      else
        (let rem =
           let uu___2 = FStar_Compiler_Util.smap_keys d in
           FStar_Compiler_List.filter
             (fun f ->
                Prims.op_Negation (FStar_Compiler_List.contains f black))
             uu___2 in
         let root =
           FStar_Compiler_List.nth rem
             ((FStar_Compiler_List.length rem) - Prims.int_one) in
         let uu___2 = topsort d [] black root in
         match uu___2 with
         | (grey, black1) ->
             (if (FStar_Compiler_List.length grey) <> Prims.int_zero
              then
                FStar_Compiler_Effect.failwith
                  "topsort_all: not all files are reachable"
              else ();
              topsort_all d black1))
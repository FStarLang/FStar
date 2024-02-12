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
  FStar_Extraction_ML_Syntax.mlletbinding ->
    Prims.string FStar_Compiler_Set.set)
  =
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
let (mlmodule1_name :
  FStar_Extraction_ML_Syntax.mlmodule1 ->
    FStar_Extraction_ML_Syntax.mlsymbol Prims.list)
  =
  fun m ->
    match m.FStar_Extraction_ML_Syntax.mlmodule1_m with
    | FStar_Extraction_ML_Syntax.MLM_Ty l ->
        FStar_Compiler_List.map
          (fun t -> t.FStar_Extraction_ML_Syntax.tydecl_name) l
    | FStar_Extraction_ML_Syntax.MLM_Let (uu___, lbs) ->
        FStar_Compiler_List.map
          (fun lb -> lb.FStar_Extraction_ML_Syntax.mllb_name) lbs
    | FStar_Extraction_ML_Syntax.MLM_Exn (s, uu___) -> [s]
    | FStar_Extraction_ML_Syntax.MLM_Top uu___ -> []
    | FStar_Extraction_ML_Syntax.MLM_Loc uu___ -> []
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
let (extract_one :
  Pulse2Rust_Env.env ->
    Prims.string ->
      FStar_Extraction_ML_UEnv.binding Prims.list ->
        FStar_Extraction_ML_Syntax.mlmodule ->
          (Prims.string * Pulse2Rust_Env.env))
  =
  fun g ->
    fun mname ->
      fun gamma ->
        fun decls ->
          let uu___ =
            FStar_Compiler_List.fold_left
              (fun uu___1 ->
                 fun d ->
                   match uu___1 with
                   | (items, g1) ->
                       let uu___2 =
                         let uu___3 =
                           decl_reachable g1.Pulse2Rust_Env.reachable_defs
                             mname d in
                         Prims.op_Negation uu___3 in
                       if uu___2
                       then (items, g1)
                       else
                         (match d.FStar_Extraction_ML_Syntax.mlmodule1_m with
                          | FStar_Extraction_ML_Syntax.MLM_Let
                              (FStar_Extraction_ML_Syntax.NonRec,
                               {
                                 FStar_Extraction_ML_Syntax.mllb_name =
                                   mllb_name;
                                 FStar_Extraction_ML_Syntax.mllb_tysc =
                                   uu___4;
                                 FStar_Extraction_ML_Syntax.mllb_add_unit =
                                   uu___5;
                                 FStar_Extraction_ML_Syntax.mllb_def = uu___6;
                                 FStar_Extraction_ML_Syntax.mllb_attrs =
                                   uu___7;
                                 FStar_Extraction_ML_Syntax.mllb_meta =
                                   uu___8;
                                 FStar_Extraction_ML_Syntax.print_typ =
                                   uu___9;_}::[])
                              when
                              (FStar_Compiler_Util.starts_with mllb_name
                                 "uu___is_")
                                ||
                                (FStar_Compiler_Util.starts_with mllb_name
                                   "__proj__")
                              -> (items, g1)
                          | FStar_Extraction_ML_Syntax.MLM_Let lb ->
                              let uu___4 =
                                Pulse2Rust_Extract.extract_top_level_lb g1 lb in
                              (match uu___4 with
                               | (f, g2) ->
                                   ((FStar_Compiler_List.op_At items [f]),
                                     g2))
                          | FStar_Extraction_ML_Syntax.MLM_Loc uu___4 ->
                              (items, g1)
                          | FStar_Extraction_ML_Syntax.MLM_Ty td ->
                              let uu___4 =
                                Pulse2Rust_Extract.extract_mltydecl g1
                                  d.FStar_Extraction_ML_Syntax.mlmodule1_attrs
                                  td in
                              (match uu___4 with
                               | (d_items, g2) ->
                                   ((FStar_Compiler_List.op_At items d_items),
                                     g2))
                          | uu___4 ->
                              let uu___5 =
                                let uu___6 =
                                  FStar_Extraction_ML_Syntax.mlmodule1_to_string
                                    d in
                                FStar_Compiler_Util.format1
                                  "top level decl %s" uu___6 in
                              Pulse2Rust_Env.fail_nyi uu___5)) ([], g) decls in
          match uu___ with
          | (items, env) ->
              let f = Pulse2Rust_Rust_Syntax.mk_file "a.rs" items in
              let s = RustBindings.file_to_rust f in (s, env)
let (file_to_module_name : Prims.string -> Prims.string) =
  fun f ->
    let suffix = ".ast" in
    let s = FStar_Compiler_Util.basename f in
    let s1 =
      FStar_Compiler_String.substring s Prims.int_zero
        ((FStar_Compiler_String.length s) -
           (FStar_Compiler_String.length suffix)) in
    FStar_Compiler_Util.replace_chars s1 95 "."
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
let (read_all_ast_files : Prims.string Prims.list -> Pulse2Rust_Env.dict) =
  fun files ->
    let d = FStar_Compiler_Util.smap_create (Prims.of_int (100)) in
    FStar_Compiler_List.iter
      (fun f ->
         let contents =
           let uu___1 = FStar_Compiler_Util.load_value_from_file f in
           match uu___1 with
           | FStar_Pervasives_Native.Some r -> r
           | FStar_Pervasives_Native.None ->
               let uu___2 =
                 FStar_Compiler_Util.format1 "Could not load file %s" f in
               FStar_Compiler_Effect.failwith uu___2 in
         let uu___1 = file_to_module_name f in
         FStar_Compiler_Util.smap_add d uu___1 contents) files;
    d
let (build_decls_dict :
  Pulse2Rust_Env.dict ->
    FStar_Extraction_ML_Syntax.mlmodule1 FStar_Compiler_Util.smap)
  =
  fun d ->
    let dd = FStar_Compiler_Util.smap_create (Prims.of_int (100)) in
    FStar_Compiler_Util.smap_iter d
      (fun module_nm ->
         fun uu___1 ->
           match uu___1 with
           | (uu___2, uu___3, decls) ->
               FStar_Compiler_List.iter
                 (fun decl ->
                    let uu___4 = mlmodule1_name decl in
                    FStar_Compiler_List.iter
                      (fun decl_nm ->
                         FStar_Compiler_Util.smap_add dd
                           (Prims.strcat module_nm (Prims.strcat "." decl_nm))
                           decl) uu___4) decls);
    dd
let rec (collect_reachable_defs_aux :
  FStar_Extraction_ML_Syntax.mlmodule1 FStar_Compiler_Util.smap ->
    Pulse2Rust_Env.reachable_defs ->
      Pulse2Rust_Env.reachable_defs -> Pulse2Rust_Env.reachable_defs)
  =
  fun dd ->
    fun worklist ->
      fun reachable_defs ->
        let uu___ =
          FStar_Compiler_Set.is_empty FStar_Class_Ord.ord_string worklist in
        if uu___
        then reachable_defs
        else
          (let uu___2 =
             FStar_Compiler_Set.elems FStar_Class_Ord.ord_string worklist in
           match uu___2 with
           | hd::uu___3 ->
               let worklist1 =
                 FStar_Compiler_Set.remove FStar_Class_Ord.ord_string hd
                   worklist in
               let reachable_defs1 =
                 FStar_Compiler_Set.add FStar_Class_Ord.ord_string hd
                   reachable_defs in
               let worklist2 =
                 let hd_decl = FStar_Compiler_Util.smap_try_find dd hd in
                 match hd_decl with
                 | FStar_Pervasives_Native.None -> worklist1
                 | FStar_Pervasives_Native.Some hd_decl1 ->
                     let hd_reachable_defs =
                       reachable_defs_mlmodule1 hd_decl1 in
                     let uu___4 =
                       FStar_Compiler_Set.elems FStar_Class_Ord.ord_string
                         hd_reachable_defs in
                     FStar_Compiler_List.fold_left
                       (fun worklist3 ->
                          fun def ->
                            let uu___5 =
                              (FStar_Compiler_Set.mem
                                 FStar_Class_Ord.ord_string def
                                 reachable_defs1)
                                ||
                                (FStar_Compiler_Set.mem
                                   FStar_Class_Ord.ord_string def worklist3) in
                            if uu___5
                            then worklist3
                            else
                              FStar_Compiler_Set.add
                                FStar_Class_Ord.ord_string def worklist3)
                       worklist1 uu___4 in
               collect_reachable_defs_aux dd worklist2 reachable_defs1)
let (collect_reachable_defs :
  Pulse2Rust_Env.dict -> Prims.string -> Pulse2Rust_Env.reachable_defs) =
  fun d ->
    fun root_module ->
      let dd = build_decls_dict d in
      let root_decls =
        let uu___ =
          let uu___1 = FStar_Compiler_Util.smap_try_find d root_module in
          FStar_Compiler_Util.must uu___1 in
        match uu___ with | (uu___1, uu___2, decls) -> decls in
      let worklist =
        FStar_Compiler_List.fold_left
          (fun worklist1 ->
             fun decl ->
               let uu___ =
                 let uu___1 = mlmodule1_name decl in
                 FStar_Compiler_List.map
                   (fun s -> Prims.strcat root_module (Prims.strcat "." s))
                   uu___1 in
               FStar_Compiler_Set.addn FStar_Class_Ord.ord_string uu___
                 worklist1) empty_defs root_decls in
      collect_reachable_defs_aux dd worklist empty_defs
let (rust_file_name : Prims.string -> Prims.string) =
  fun mname ->
    let s =
      FStar_Compiler_String.lowercase
        (FStar_Compiler_Util.replace_char mname 46 95) in
    FStar_Compiler_Util.strcat s ".rs"
let (header : Prims.string) =
  "////\n////\n//// This file is generated by the Pulse2Rust tool\n////\n////\n"
let (extract : Prims.string Prims.list -> Prims.string -> unit) =
  fun files ->
    fun odir ->
      let d = read_all_ast_files files in
      let all_modules = topsort_all d [] in
      let uu___ = all_modules in
      match uu___ with
      | root_module::uu___1 ->
          let reachable_defs = collect_reachable_defs d root_module in
          let g = Pulse2Rust_Env.empty_env d all_modules reachable_defs in
          let uu___2 =
            FStar_Compiler_List.fold_left
              (fun uu___3 ->
                 fun f ->
                   match uu___3 with
                   | (g1, all_rust_files) ->
                       let uu___4 =
                         let uu___5 = FStar_Compiler_Util.smap_try_find d f in
                         FStar_Compiler_Util.must uu___5 in
                       (match uu___4 with
                        | (uu___5, bs, ds) ->
                            let uu___6 = extract_one g1 f bs ds in
                            (match uu___6 with
                             | (s, g2) ->
                                 let rust_fname =
                                   let uu___7 = rust_file_name f in
                                   FStar_Compiler_Util.concat_dir_filename
                                     odir uu___7 in
                                 let rust_f =
                                   FStar_Compiler_Util.open_file_for_writing
                                     rust_fname in
                                 (FStar_Compiler_Util.append_to_file rust_f
                                    header;
                                  FStar_Compiler_Util.append_to_file rust_f s;
                                  FStar_Compiler_Util.close_out_channel
                                    rust_f;
                                  (g2, (rust_fname :: all_rust_files))))))
              (g, []) all_modules in
          (match uu___2 with
           | (uu___3, all_rust_files) ->
               FStar_Compiler_Util.print1 "\n\nExtracted: %s\n\n"
                 (FStar_Compiler_String.concat " " all_rust_files))
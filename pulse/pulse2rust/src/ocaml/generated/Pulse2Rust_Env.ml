open Prims
let fail : 'a . Prims.string -> 'a =
  fun s ->
    let uu___ =
      FStarC_Compiler_Util.format1 "Pulse to Rust extraction failed: %s" s in
    failwith uu___
let fail_nyi : 'a . Prims.string -> 'a =
  fun s ->
    let uu___ =
      FStarC_Compiler_Util.format1
        "Pulse to Rust extraction failed: no support yet for %s" s in
    failwith uu___
type var = Prims.string
type binding = (var * Pulse2Rust_Rust_Syntax.typ * Prims.bool)
type reachable_defs = Prims.string FStarC_Compiler_RBSet.t
let (reachable_defs_to_string : reachable_defs -> Prims.string) =
  fun d ->
    let uu___ =
      let uu___1 =
        FStarC_Class_Setlike.elems ()
          (Obj.magic
             (FStarC_Compiler_RBSet.setlike_rbset FStarC_Class_Ord.ord_string))
          (Obj.magic d) in
      FStarC_Compiler_String.concat ";" uu___1 in
    FStarC_Compiler_Util.format1 "[%s]" uu___
type dict =
  (Prims.string Prims.list * FStarC_Extraction_ML_UEnv.binding Prims.list *
    FStarC_Extraction_ML_Syntax.mlmodule) FStarC_Compiler_Util.smap
type env =
  {
  external_libs: Prims.string Prims.list ;
  fns: (Prims.string * Pulse2Rust_Rust_Syntax.fn_signature) Prims.list ;
  statics: (Prims.string * Pulse2Rust_Rust_Syntax.typ) Prims.list ;
  gamma: binding Prims.list ;
  d: dict ;
  all_modules: Prims.string Prims.list ;
  reachable_defs: reachable_defs }
let (__proj__Mkenv__item__external_libs : env -> Prims.string Prims.list) =
  fun projectee ->
    match projectee with
    | { external_libs; fns; statics; gamma; d; all_modules;
        reachable_defs = reachable_defs1;_} -> external_libs
let (__proj__Mkenv__item__fns :
  env -> (Prims.string * Pulse2Rust_Rust_Syntax.fn_signature) Prims.list) =
  fun projectee ->
    match projectee with
    | { external_libs; fns; statics; gamma; d; all_modules;
        reachable_defs = reachable_defs1;_} -> fns
let (__proj__Mkenv__item__statics :
  env -> (Prims.string * Pulse2Rust_Rust_Syntax.typ) Prims.list) =
  fun projectee ->
    match projectee with
    | { external_libs; fns; statics; gamma; d; all_modules;
        reachable_defs = reachable_defs1;_} -> statics
let (__proj__Mkenv__item__gamma : env -> binding Prims.list) =
  fun projectee ->
    match projectee with
    | { external_libs; fns; statics; gamma; d; all_modules;
        reachable_defs = reachable_defs1;_} -> gamma
let (__proj__Mkenv__item__d : env -> dict) =
  fun projectee ->
    match projectee with
    | { external_libs; fns; statics; gamma; d; all_modules;
        reachable_defs = reachable_defs1;_} -> d
let (__proj__Mkenv__item__all_modules : env -> Prims.string Prims.list) =
  fun projectee ->
    match projectee with
    | { external_libs; fns; statics; gamma; d; all_modules;
        reachable_defs = reachable_defs1;_} -> all_modules
let (__proj__Mkenv__item__reachable_defs : env -> reachable_defs) =
  fun projectee ->
    match projectee with
    | { external_libs; fns; statics; gamma; d; all_modules;
        reachable_defs = reachable_defs1;_} -> reachable_defs1
let (empty_env :
  Prims.string Prims.list ->
    dict -> Prims.string Prims.list -> reachable_defs -> env)
  =
  fun external_libs ->
    fun d ->
      fun all_modules ->
        fun reachable_defs1 ->
          {
            external_libs;
            fns = [];
            statics = [];
            gamma = [];
            d;
            all_modules;
            reachable_defs = reachable_defs1
          }
let (lookup_global_fn :
  env ->
    Prims.string ->
      Pulse2Rust_Rust_Syntax.fn_signature FStar_Pervasives_Native.option)
  =
  fun g ->
    fun s ->
      let uu___ =
        FStarC_Compiler_List.tryFind
          (fun uu___1 -> match uu___1 with | (f, uu___2) -> f = s) g.fns in
      FStarC_Compiler_Util.map_option
        (fun uu___1 -> match uu___1 with | (uu___2, t) -> t) uu___
let (lookup_local :
  env ->
    Prims.string ->
      (Pulse2Rust_Rust_Syntax.typ * Prims.bool)
        FStar_Pervasives_Native.option)
  =
  fun g ->
    fun s ->
      let uu___ =
        FStarC_Compiler_List.tryFind
          (fun uu___1 -> match uu___1 with | (x, uu___2, uu___3) -> x = s)
          g.gamma in
      FStarC_Compiler_Util.map_option
        (fun uu___1 -> match uu___1 with | (uu___2, t, b) -> (t, b)) uu___
let (push_fn :
  env -> Prims.string -> Pulse2Rust_Rust_Syntax.fn_signature -> env) =
  fun g ->
    fun s ->
      fun t ->
        {
          external_libs = (g.external_libs);
          fns = ((s, t) :: (g.fns));
          statics = (g.statics);
          gamma = (g.gamma);
          d = (g.d);
          all_modules = (g.all_modules);
          reachable_defs = (g.reachable_defs)
        }
let (push_static : env -> Prims.string -> Pulse2Rust_Rust_Syntax.typ -> env)
  =
  fun g ->
    fun s ->
      fun t ->
        {
          external_libs = (g.external_libs);
          fns = (g.fns);
          statics = ((s, t) :: (g.statics));
          gamma = (g.gamma);
          d = (g.d);
          all_modules = (g.all_modules);
          reachable_defs = (g.reachable_defs)
        }
let (push_local :
  env -> Prims.string -> Pulse2Rust_Rust_Syntax.typ -> Prims.bool -> env) =
  fun g ->
    fun s ->
      fun t ->
        fun is_mut ->
          {
            external_libs = (g.external_libs);
            fns = (g.fns);
            statics = (g.statics);
            gamma = ((s, t, is_mut) :: (g.gamma));
            d = (g.d);
            all_modules = (g.all_modules);
            reachable_defs = (g.reachable_defs)
          }
let (is_external_lib : env -> Prims.string -> Prims.bool) =
  fun g -> fun s -> FStarC_Compiler_List.contains s g.external_libs
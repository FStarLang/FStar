open Prims
type codegen_t =
  | OCaml 
  | FSharp 
  | Krml 
  | Plugin 
  | Extension 
let (uu___is_OCaml : codegen_t -> Prims.bool) =
  fun projectee -> match projectee with | OCaml -> true | uu___ -> false
let (uu___is_FSharp : codegen_t -> Prims.bool) =
  fun projectee -> match projectee with | FSharp -> true | uu___ -> false
let (uu___is_Krml : codegen_t -> Prims.bool) =
  fun projectee -> match projectee with | Krml -> true | uu___ -> false
let (uu___is_Plugin : codegen_t -> Prims.bool) =
  fun projectee -> match projectee with | Plugin -> true | uu___ -> false
let (uu___is_Extension : codegen_t -> Prims.bool) =
  fun projectee -> match projectee with | Extension -> true | uu___ -> false
type split_queries_t =
  | No 
  | OnFailure 
  | Always 
let (uu___is_No : split_queries_t -> Prims.bool) =
  fun projectee -> match projectee with | No -> true | uu___ -> false
let (uu___is_OnFailure : split_queries_t -> Prims.bool) =
  fun projectee -> match projectee with | OnFailure -> true | uu___ -> false
let (uu___is_Always : split_queries_t -> Prims.bool) =
  fun projectee -> match projectee with | Always -> true | uu___ -> false
type message_format_t =
  | Json 
  | Human 
let (uu___is_Json : message_format_t -> Prims.bool) =
  fun projectee -> match projectee with | Json -> true | uu___ -> false
let (uu___is_Human : message_format_t -> Prims.bool) =
  fun projectee -> match projectee with | Human -> true | uu___ -> false
type option_val =
  | Bool of Prims.bool 
  | String of Prims.string 
  | Path of Prims.string 
  | Int of Prims.int 
  | List of option_val Prims.list 
  | Unset 
let (uu___is_Bool : option_val -> Prims.bool) =
  fun projectee -> match projectee with | Bool _0 -> true | uu___ -> false
let (__proj__Bool__item___0 : option_val -> Prims.bool) =
  fun projectee -> match projectee with | Bool _0 -> _0
let (uu___is_String : option_val -> Prims.bool) =
  fun projectee -> match projectee with | String _0 -> true | uu___ -> false
let (__proj__String__item___0 : option_val -> Prims.string) =
  fun projectee -> match projectee with | String _0 -> _0
let (uu___is_Path : option_val -> Prims.bool) =
  fun projectee -> match projectee with | Path _0 -> true | uu___ -> false
let (__proj__Path__item___0 : option_val -> Prims.string) =
  fun projectee -> match projectee with | Path _0 -> _0
let (uu___is_Int : option_val -> Prims.bool) =
  fun projectee -> match projectee with | Int _0 -> true | uu___ -> false
let (__proj__Int__item___0 : option_val -> Prims.int) =
  fun projectee -> match projectee with | Int _0 -> _0
let (uu___is_List : option_val -> Prims.bool) =
  fun projectee -> match projectee with | List _0 -> true | uu___ -> false
let (__proj__List__item___0 : option_val -> option_val Prims.list) =
  fun projectee -> match projectee with | List _0 -> _0
let (uu___is_Unset : option_val -> Prims.bool) =
  fun projectee -> match projectee with | Unset -> true | uu___ -> false
type optionstate = option_val FStarC_Compiler_Util.psmap
type opt_type =
  | Const of option_val 
  | IntStr of Prims.string 
  | BoolStr 
  | PathStr of Prims.string 
  | SimpleStr of Prims.string 
  | EnumStr of Prims.string Prims.list 
  | OpenEnumStr of (Prims.string Prims.list * Prims.string) 
  | PostProcessed of ((option_val -> option_val) * opt_type) 
  | Accumulated of opt_type 
  | ReverseAccumulated of opt_type 
  | WithSideEffect of ((unit -> unit) * opt_type) 
let (uu___is_Const : opt_type -> Prims.bool) =
  fun projectee -> match projectee with | Const _0 -> true | uu___ -> false
let (__proj__Const__item___0 : opt_type -> option_val) =
  fun projectee -> match projectee with | Const _0 -> _0
let (uu___is_IntStr : opt_type -> Prims.bool) =
  fun projectee -> match projectee with | IntStr _0 -> true | uu___ -> false
let (__proj__IntStr__item___0 : opt_type -> Prims.string) =
  fun projectee -> match projectee with | IntStr _0 -> _0
let (uu___is_BoolStr : opt_type -> Prims.bool) =
  fun projectee -> match projectee with | BoolStr -> true | uu___ -> false
let (uu___is_PathStr : opt_type -> Prims.bool) =
  fun projectee -> match projectee with | PathStr _0 -> true | uu___ -> false
let (__proj__PathStr__item___0 : opt_type -> Prims.string) =
  fun projectee -> match projectee with | PathStr _0 -> _0
let (uu___is_SimpleStr : opt_type -> Prims.bool) =
  fun projectee ->
    match projectee with | SimpleStr _0 -> true | uu___ -> false
let (__proj__SimpleStr__item___0 : opt_type -> Prims.string) =
  fun projectee -> match projectee with | SimpleStr _0 -> _0
let (uu___is_EnumStr : opt_type -> Prims.bool) =
  fun projectee -> match projectee with | EnumStr _0 -> true | uu___ -> false
let (__proj__EnumStr__item___0 : opt_type -> Prims.string Prims.list) =
  fun projectee -> match projectee with | EnumStr _0 -> _0
let (uu___is_OpenEnumStr : opt_type -> Prims.bool) =
  fun projectee ->
    match projectee with | OpenEnumStr _0 -> true | uu___ -> false
let (__proj__OpenEnumStr__item___0 :
  opt_type -> (Prims.string Prims.list * Prims.string)) =
  fun projectee -> match projectee with | OpenEnumStr _0 -> _0
let (uu___is_PostProcessed : opt_type -> Prims.bool) =
  fun projectee ->
    match projectee with | PostProcessed _0 -> true | uu___ -> false
let (__proj__PostProcessed__item___0 :
  opt_type -> ((option_val -> option_val) * opt_type)) =
  fun projectee -> match projectee with | PostProcessed _0 -> _0
let (uu___is_Accumulated : opt_type -> Prims.bool) =
  fun projectee ->
    match projectee with | Accumulated _0 -> true | uu___ -> false
let (__proj__Accumulated__item___0 : opt_type -> opt_type) =
  fun projectee -> match projectee with | Accumulated _0 -> _0
let (uu___is_ReverseAccumulated : opt_type -> Prims.bool) =
  fun projectee ->
    match projectee with | ReverseAccumulated _0 -> true | uu___ -> false
let (__proj__ReverseAccumulated__item___0 : opt_type -> opt_type) =
  fun projectee -> match projectee with | ReverseAccumulated _0 -> _0
let (uu___is_WithSideEffect : opt_type -> Prims.bool) =
  fun projectee ->
    match projectee with | WithSideEffect _0 -> true | uu___ -> false
let (__proj__WithSideEffect__item___0 :
  opt_type -> ((unit -> unit) * opt_type)) =
  fun projectee -> match projectee with | WithSideEffect _0 -> _0
let (debug_embedding : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Util.mk_ref false
let (eager_embedding : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Util.mk_ref false
let (__unit_tests__ : Prims.bool FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Util.mk_ref false
let (__unit_tests : unit -> Prims.bool) =
  fun uu___ -> FStarC_Compiler_Effect.op_Bang __unit_tests__
let (__set_unit_tests : unit -> unit) =
  fun uu___ -> FStarC_Compiler_Effect.op_Colon_Equals __unit_tests__ true
let (__clear_unit_tests : unit -> unit) =
  fun uu___ -> FStarC_Compiler_Effect.op_Colon_Equals __unit_tests__ false
let (as_bool : option_val -> Prims.bool) =
  fun uu___ ->
    match uu___ with
    | Bool b -> b
    | uu___1 -> failwith "Impos: expected Bool"
let (as_int : option_val -> Prims.int) =
  fun uu___ ->
    match uu___ with | Int b -> b | uu___1 -> failwith "Impos: expected Int"
let (as_string : option_val -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | String b -> b
    | Path b -> FStarC_Common.try_convert_file_name_to_mixed b
    | uu___1 -> failwith "Impos: expected String"
let (as_list' : option_val -> option_val Prims.list) =
  fun uu___ ->
    match uu___ with
    | List ts -> ts
    | uu___1 -> failwith "Impos: expected List"
let as_list :
  'uuuuu . (option_val -> 'uuuuu) -> option_val -> 'uuuuu Prims.list =
  fun as_t ->
    fun x -> let uu___ = as_list' x in FStarC_Compiler_List.map as_t uu___
let as_option :
  'uuuuu .
    (option_val -> 'uuuuu) ->
      option_val -> 'uuuuu FStar_Pervasives_Native.option
  =
  fun as_t ->
    fun uu___ ->
      match uu___ with
      | Unset -> FStar_Pervasives_Native.None
      | v -> let uu___1 = as_t v in FStar_Pervasives_Native.Some uu___1
let (as_comma_string_list : option_val -> Prims.string Prims.list) =
  fun uu___ ->
    match uu___ with
    | List ls ->
        let uu___1 =
          FStarC_Compiler_List.map
            (fun l ->
               let uu___2 = as_string l in
               FStarC_Compiler_Util.split uu___2 ",") ls in
        FStarC_Compiler_List.flatten uu___1
    | uu___1 -> failwith "Impos: expected String (comma list)"
let copy_optionstate :
  'uuuuu .
    'uuuuu FStarC_Compiler_Util.smap -> 'uuuuu FStarC_Compiler_Util.smap
  = fun m -> FStarC_Compiler_Util.smap_copy m
type history1 =
  (FStarC_Compiler_Debug.saved_state * FStarC_Options_Ext.ext_state *
    optionstate)
let (fstar_options : optionstate FStarC_Compiler_Effect.ref) =
  let uu___ = FStarC_Compiler_Util.psmap_empty () in
  FStarC_Compiler_Util.mk_ref uu___
let (history : history1 Prims.list Prims.list FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Util.mk_ref []
let (peek : unit -> optionstate) =
  fun uu___ -> FStarC_Compiler_Effect.op_Bang fstar_options
let (internal_push : unit -> unit) =
  fun uu___ ->
    let uu___1 = FStarC_Compiler_Effect.op_Bang history in
    match uu___1 with
    | lev1::rest ->
        let newhd =
          let uu___2 = FStarC_Compiler_Debug.snapshot () in
          let uu___3 = FStarC_Options_Ext.save () in
          let uu___4 = FStarC_Compiler_Effect.op_Bang fstar_options in
          (uu___2, uu___3, uu___4) in
        FStarC_Compiler_Effect.op_Colon_Equals history ((newhd :: lev1) ::
          rest)
let (internal_pop : unit -> Prims.bool) =
  fun uu___ ->
    let uu___1 = FStarC_Compiler_Effect.op_Bang history in
    match uu___1 with
    | lev1::rest ->
        (match lev1 with
         | [] -> false
         | (dbg, ext, opts)::lev1' ->
             (FStarC_Compiler_Debug.restore dbg;
              FStarC_Options_Ext.restore ext;
              FStarC_Compiler_Effect.op_Colon_Equals fstar_options opts;
              FStarC_Compiler_Effect.op_Colon_Equals history (lev1' :: rest);
              true))
let (push : unit -> unit) =
  fun uu___ ->
    internal_push ();
    (let uu___2 = FStarC_Compiler_Effect.op_Bang history in
     match uu___2 with
     | lev1::uu___3 ->
         ((let uu___5 =
             let uu___6 = FStarC_Compiler_Effect.op_Bang history in lev1 ::
               uu___6 in
           FStarC_Compiler_Effect.op_Colon_Equals history uu___5);
          (let uu___6 = internal_pop () in ())))
let (pop : unit -> unit) =
  fun uu___ ->
    let uu___1 = FStarC_Compiler_Effect.op_Bang history in
    match uu___1 with
    | [] -> failwith "TOO MANY POPS!"
    | uu___2::levs ->
        (FStarC_Compiler_Effect.op_Colon_Equals history levs;
         (let uu___4 =
            let uu___5 = internal_pop () in Prims.op_Negation uu___5 in
          if uu___4 then failwith "aaa!!!" else ()))
let (set : optionstate -> unit) =
  fun o -> FStarC_Compiler_Effect.op_Colon_Equals fstar_options o
let (depth : unit -> Prims.int) =
  fun uu___ ->
    let uu___1 = FStarC_Compiler_Effect.op_Bang history in
    match uu___1 with | lev::uu___2 -> FStarC_Compiler_List.length lev
let (snapshot : unit -> (Prims.int * unit)) =
  fun uu___ -> FStarC_Common.snapshot push history ()
let (rollback : Prims.int FStar_Pervasives_Native.option -> unit) =
  fun depth1 -> FStarC_Common.rollback pop history depth1
let (set_option : Prims.string -> option_val -> unit) =
  fun k ->
    fun v ->
      let map = peek () in
      if k = "report_assumes"
      then
        let uu___ = FStarC_Compiler_Util.psmap_try_find map k in
        match uu___ with
        | FStar_Pervasives_Native.Some (String "error") -> ()
        | uu___1 ->
            let uu___2 = FStarC_Compiler_Util.psmap_add map k v in
            FStarC_Compiler_Effect.op_Colon_Equals fstar_options uu___2
      else
        (let uu___1 = FStarC_Compiler_Util.psmap_add map k v in
         FStarC_Compiler_Effect.op_Colon_Equals fstar_options uu___1)
let (set_option' : (Prims.string * option_val) -> unit) =
  fun uu___ -> match uu___ with | (k, v) -> set_option k v
let (set_admit_smt_queries : Prims.bool -> unit) =
  fun b -> set_option "admit_smt_queries" (Bool b)
let (defaults : (Prims.string * option_val) Prims.list) =
  [("abort_on", (Int Prims.int_zero));
  ("admit_smt_queries", (Bool false));
  ("admit_except", Unset);
  ("disallow_unification_guards", (Bool false));
  ("already_cached", Unset);
  ("cache_checked_modules", (Bool false));
  ("cache_dir", Unset);
  ("cache_off", (Bool false));
  ("compat_pre_core", Unset);
  ("compat_pre_typed_indexed_effects", (Bool false));
  ("print_cache_version", (Bool false));
  ("cmi", (Bool false));
  ("codegen", Unset);
  ("codegen-lib", (List []));
  ("defensive", (String "no"));
  ("debug", (List []));
  ("debug_all", (Bool false));
  ("debug_all_modules", (Bool false));
  ("dep", Unset);
  ("detail_errors", (Bool false));
  ("detail_hint_replay", (Bool false));
  ("dump_module", (List []));
  ("eager_subtyping", (Bool false));
  ("error_contexts", (Bool false));
  ("expose_interfaces", (Bool false));
  ("message_format", (String "human"));
  ("ext", Unset);
  ("extract", Unset);
  ("extract_all", (Bool false));
  ("extract_module", (List []));
  ("extract_namespace", (List []));
  ("full_context_dependency", (Bool true));
  ("hide_uvar_nums", (Bool false));
  ("hint_hook", Unset);
  ("hint_info", (Bool false));
  ("hint_dir", Unset);
  ("hint_file", Unset);
  ("in", (Bool false));
  ("ide", (Bool false));
  ("ide_id_info_off", (Bool false));
  ("lsp", (Bool false));
  ("include", (List []));
  ("print", (Bool false));
  ("print_in_place", (Bool false));
  ("force", (Bool false));
  ("fuel", Unset);
  ("ifuel", Unset);
  ("initial_fuel", (Int (Prims.of_int (2))));
  ("initial_ifuel", (Int Prims.int_one));
  ("keep_query_captions", (Bool true));
  ("lax", (Bool false));
  ("load", (List []));
  ("load_cmxs", (List []));
  ("log_queries", (Bool false));
  ("log_failing_queries", (Bool false));
  ("log_types", (Bool false));
  ("max_fuel", (Int (Prims.of_int (8))));
  ("max_ifuel", (Int (Prims.of_int (2))));
  ("MLish", (Bool false));
  ("MLish_effect", (String "FStar.Compiler.Effect"));
  ("no_default_includes", (Bool false));
  ("no_extract", (List []));
  ("no_location_info", (Bool false));
  ("no_smt", (Bool false));
  ("no_plugins", (Bool false));
  ("no_tactics", (Bool false));
  ("normalize_pure_terms_for_extraction", (Bool false));
  ("krmloutput", Unset);
  ("odir", Unset);
  ("output_deps_to", Unset);
  ("prims", Unset);
  ("pretype", (Bool true));
  ("prims_ref", Unset);
  ("print_bound_var_types", (Bool false));
  ("print_effect_args", (Bool false));
  ("print_expected_failures", (Bool false));
  ("print_full_names", (Bool false));
  ("print_implicits", (Bool false));
  ("print_universes", (Bool false));
  ("print_z3_statistics", (Bool false));
  ("prn", (Bool false));
  ("proof_recovery", (Bool false));
  ("quake", (Int Prims.int_zero));
  ("quake_lo", (Int Prims.int_one));
  ("quake_hi", (Int Prims.int_one));
  ("quake_keep", (Bool false));
  ("query_cache", (Bool false));
  ("query_stats", (Bool false));
  ("read_checked_file", Unset);
  ("list_plugins", (Bool false));
  ("locate", (Bool false));
  ("locate_lib", (Bool false));
  ("locate_ocaml", (Bool false));
  ("read_krml_file", Unset);
  ("record_hints", (Bool false));
  ("record_options", (Bool false));
  ("report_assumes", Unset);
  ("retry", (Bool false));
  ("reuse_hint_for", Unset);
  ("silent", (Bool false));
  ("smt", Unset);
  ("smtencoding.elim_box", (Bool false));
  ("smtencoding.nl_arith_repr", (String "boxwrap"));
  ("smtencoding.l_arith_repr", (String "boxwrap"));
  ("smtencoding.valid_intro", (Bool true));
  ("smtencoding.valid_elim", (Bool false));
  ("split_queries", (String "on_failure"));
  ("tactics_failhard", (Bool false));
  ("tactics_info", (Bool false));
  ("tactic_raw_binders", (Bool false));
  ("tactic_trace", (Bool false));
  ("tactic_trace_d", (Int Prims.int_zero));
  ("tcnorm", (Bool true));
  ("timing", (Bool false));
  ("trace_error", (Bool false));
  ("ugly", (Bool false));
  ("unthrottle_inductives", (Bool false));
  ("unsafe_tactic_exec", (Bool false));
  ("use_native_tactics", Unset);
  ("use_eq_at_higher_order", (Bool false));
  ("use_hints", (Bool false));
  ("use_hint_hashes", (Bool false));
  ("using_facts_from", Unset);
  ("verify_module", (List []));
  ("warn_default_effects", (Bool false));
  ("z3refresh", (Bool false));
  ("z3rlimit", (Int (Prims.of_int (5))));
  ("z3rlimit_factor", (Int Prims.int_one));
  ("z3seed", (Int Prims.int_zero));
  ("z3cliopt", (List []));
  ("z3smtopt", (List []));
  ("z3version", (String "4.8.5"));
  ("__no_positivity", (Bool false));
  ("__tactics_nbe", (Bool false));
  ("warn_error", (List []));
  ("use_nbe", (Bool false));
  ("use_nbe_for_extraction", (Bool false));
  ("trivial_pre_for_unannotated_effectful_fns", (Bool true));
  ("profile_group_by_decl", (Bool false));
  ("profile_component", Unset);
  ("profile", Unset)]
let (init : unit -> unit) =
  fun uu___ ->
    FStarC_Compiler_Debug.disable_all ();
    FStarC_Options_Ext.reset ();
    (let uu___4 = FStarC_Compiler_Util.psmap_empty () in
     FStarC_Compiler_Effect.op_Colon_Equals fstar_options uu___4);
    FStarC_Compiler_List.iter set_option' defaults
let (clear : unit -> unit) =
  fun uu___ -> FStarC_Compiler_Effect.op_Colon_Equals history [[]]; init ()
let (uu___0 : unit) = clear ()
let (get_option : Prims.string -> option_val) =
  fun s ->
    let uu___ =
      let uu___1 = peek () in FStarC_Compiler_Util.psmap_try_find uu___1 s in
    match uu___ with
    | FStar_Pervasives_Native.None ->
        let uu___1 =
          let uu___2 = FStarC_Compiler_String.op_Hat s " not found" in
          FStarC_Compiler_String.op_Hat "Impossible: option " uu___2 in
        failwith uu___1
    | FStar_Pervasives_Native.Some s1 -> s1
let rec (option_val_to_string : option_val -> Prims.string) =
  fun v ->
    match v with
    | Bool b ->
        let uu___ = FStarC_Class_Show.show FStarC_Class_Show.showable_bool b in
        FStarC_Compiler_String.op_Hat "Bool " uu___
    | String s ->
        let uu___ =
          FStarC_Class_Show.show FStarC_Class_Show.showable_string s in
        FStarC_Compiler_String.op_Hat "String " uu___
    | Path s ->
        let uu___ =
          FStarC_Class_Show.show FStarC_Class_Show.showable_string s in
        FStarC_Compiler_String.op_Hat "Path " uu___
    | Int i ->
        let uu___ = FStarC_Class_Show.show FStarC_Class_Show.showable_int i in
        FStarC_Compiler_String.op_Hat "Int " uu___
    | List vs ->
        let uu___ = (FStarC_Common.string_of_list ()) option_val_to_string vs in
        FStarC_Compiler_String.op_Hat "List " uu___
    | Unset -> "Unset"
let (showable_option_val : option_val FStarC_Class_Show.showable) =
  { FStarC_Class_Show.show = option_val_to_string }
let rec (eq_option_val : option_val -> option_val -> Prims.bool) =
  fun v1 ->
    fun v2 ->
      match (v1, v2) with
      | (Bool x1, Bool x2) ->
          FStarC_Class_Deq.op_Equals_Question FStarC_Class_Deq.deq_bool x1 x2
      | (String x1, String x2) ->
          FStarC_Class_Deq.op_Equals_Question FStarC_Class_Deq.deq_string x1
            x2
      | (Path x1, Path x2) ->
          FStarC_Class_Deq.op_Equals_Question FStarC_Class_Deq.deq_string x1
            x2
      | (Int x1, Int x2) ->
          FStarC_Class_Deq.op_Equals_Question FStarC_Class_Deq.deq_int x1 x2
      | (Unset, Unset) -> true
      | (List x1, List x2) -> FStarC_Common.eq_list eq_option_val x1 x2
      | (uu___, uu___1) -> false
let (deq_option_val : option_val FStarC_Class_Deq.deq) =
  { FStarC_Class_Deq.op_Equals_Question = eq_option_val }
let rec list_try_find :
  'a 'b .
    'a FStarC_Class_Deq.deq ->
      'a -> ('a * 'b) Prims.list -> 'b FStar_Pervasives_Native.option
  =
  fun uu___ ->
    fun k ->
      fun l ->
        match l with
        | [] -> FStar_Pervasives_Native.None
        | (k', v')::l' ->
            let uu___1 = FStarC_Class_Deq.op_Equals_Question uu___ k k' in
            if uu___1
            then FStar_Pervasives_Native.Some v'
            else list_try_find uu___ k l'
let (show_options : unit -> Prims.string) =
  fun uu___ ->
    let s = peek () in
    let kvs =
      let uu___1 = FStarC_Common.psmap_keys s in
      Obj.magic
        (FStarC_Class_Monad.op_let_Bang FStarC_Class_Monad.monad_list () ()
           (Obj.magic uu___1)
           (fun uu___2 ->
              (fun k ->
                 let k = Obj.magic k in
                 if k = "verify_module"
                 then Obj.magic (Obj.repr [])
                 else
                   Obj.magic
                     (Obj.repr
                        (let v =
                           let uu___3 =
                             FStarC_Compiler_Util.psmap_try_find s k in
                           FStarC_Compiler_Util.must uu___3 in
                         let v0 =
                           list_try_find FStarC_Class_Deq.deq_string k
                             defaults in
                         let uu___3 =
                           FStarC_Class_Deq.op_Equals_Question
                             (FStarC_Class_Deq.deq_option deq_option_val) v0
                             (FStar_Pervasives_Native.Some v) in
                         if uu___3
                         then Obj.repr []
                         else
                           Obj.repr
                             (FStarC_Class_Monad.return
                                FStarC_Class_Monad.monad_list ()
                                (Obj.magic (k, v)))))) uu___2)) in
    let rec show_optionval v =
      match v with
      | String s1 ->
          let uu___1 = FStarC_Compiler_String.op_Hat s1 "\"" in
          FStarC_Compiler_String.op_Hat "\"" uu___1
      | Bool b -> FStarC_Class_Show.show FStarC_Class_Show.showable_bool b
      | Int i -> FStarC_Class_Show.show FStarC_Class_Show.showable_int i
      | Path s1 -> s1
      | List s1 ->
          let uu___1 = FStarC_Compiler_List.map show_optionval s1 in
          FStarC_Compiler_String.concat "," uu___1
      | Unset -> "<unset>" in
    let show1 uu___1 =
      match uu___1 with
      | (k, v) ->
          let uu___2 = show_optionval v in
          FStarC_Compiler_Util.format2 "--%s %s" k uu___2 in
    let uu___1 = FStarC_Compiler_List.map show1 kvs in
    FStarC_Compiler_String.concat "\n" uu___1
let (set_verification_options : optionstate -> unit) =
  fun o ->
    let verifopts =
      ["initial_fuel";
      "max_fuel";
      "initial_ifuel";
      "max_ifuel";
      "detail_errors";
      "detail_hint_replay";
      "no_smt";
      "quake";
      "retry";
      "smtencoding.elim_box";
      "smtencoding.nl_arith_repr";
      "smtencoding.l_arith_repr";
      "smtencoding.valid_intro";
      "smtencoding.valid_elim";
      "tcnorm";
      "no_plugins";
      "no_tactics";
      "z3cliopt";
      "z3smtopt";
      "z3refresh";
      "z3rlimit";
      "z3rlimit_factor";
      "z3seed";
      "z3version";
      "trivial_pre_for_unannotated_effectful_fns"] in
    FStarC_Compiler_List.iter
      (fun k ->
         let uu___ =
           let uu___1 = FStarC_Compiler_Util.psmap_try_find o k in
           FStarC_Compiler_Util.must uu___1 in
         set_option k uu___) verifopts
let lookup_opt : 'uuuuu . Prims.string -> (option_val -> 'uuuuu) -> 'uuuuu =
  fun s -> fun c -> let uu___ = get_option s in c uu___
let (get_abort_on : unit -> Prims.int) =
  fun uu___ -> lookup_opt "abort_on" as_int
let (get_admit_smt_queries : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "admit_smt_queries" as_bool
let (get_admit_except : unit -> Prims.string FStar_Pervasives_Native.option)
  = fun uu___ -> lookup_opt "admit_except" (as_option as_string)
let (get_compat_pre_core : unit -> Prims.int FStar_Pervasives_Native.option)
  = fun uu___ -> lookup_opt "compat_pre_core" (as_option as_int)
let (get_compat_pre_typed_indexed_effects : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "compat_pre_typed_indexed_effects" as_bool
let (get_disallow_unification_guards : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "disallow_unification_guards" as_bool
let (get_already_cached :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu___ -> lookup_opt "already_cached" (as_option (as_list as_string))
let (get_cache_checked_modules : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "cache_checked_modules" as_bool
let (get_cache_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu___ -> lookup_opt "cache_dir" (as_option as_string)
let (get_cache_off : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "cache_off" as_bool
let (get_print_cache_version : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "print_cache_version" as_bool
let (get_cmi : unit -> Prims.bool) = fun uu___ -> lookup_opt "cmi" as_bool
let (get_codegen : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu___ -> lookup_opt "codegen" (as_option as_string)
let (get_codegen_lib : unit -> Prims.string Prims.list) =
  fun uu___ -> lookup_opt "codegen-lib" (as_list as_string)
let (get_defensive : unit -> Prims.string) =
  fun uu___ -> lookup_opt "defensive" as_string
let (get_dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu___ -> lookup_opt "dep" (as_option as_string)
let (get_detail_errors : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "detail_errors" as_bool
let (get_detail_hint_replay : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "detail_hint_replay" as_bool
let (get_dump_module : unit -> Prims.string Prims.list) =
  fun uu___ -> lookup_opt "dump_module" (as_list as_string)
let (get_eager_subtyping : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "eager_subtyping" as_bool
let (get_error_contexts : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "error_contexts" as_bool
let (get_expose_interfaces : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "expose_interfaces" as_bool
let (get_message_format : unit -> Prims.string) =
  fun uu___ -> lookup_opt "message_format" as_string
let (get_extract :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu___ -> lookup_opt "extract" (as_option (as_list as_string))
let (get_extract_module : unit -> Prims.string Prims.list) =
  fun uu___ -> lookup_opt "extract_module" (as_list as_string)
let (get_extract_namespace : unit -> Prims.string Prims.list) =
  fun uu___ -> lookup_opt "extract_namespace" (as_list as_string)
let (get_force : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "force" as_bool
let (get_hide_uvar_nums : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "hide_uvar_nums" as_bool
let (get_hint_info : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "hint_info" as_bool
let (get_hint_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu___ -> lookup_opt "hint_dir" (as_option as_string)
let (get_hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu___ -> lookup_opt "hint_file" (as_option as_string)
let (get_in : unit -> Prims.bool) = fun uu___ -> lookup_opt "in" as_bool
let (get_ide : unit -> Prims.bool) = fun uu___ -> lookup_opt "ide" as_bool
let (get_ide_id_info_off : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "ide_id_info_off" as_bool
let (get_lsp : unit -> Prims.bool) = fun uu___ -> lookup_opt "lsp" as_bool
let (get_include : unit -> Prims.string Prims.list) =
  fun uu___ -> lookup_opt "include" (as_list as_string)
let (get_print : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "print" as_bool
let (get_print_in_place : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "print_in_place" as_bool
let (get_initial_fuel : unit -> Prims.int) =
  fun uu___ -> lookup_opt "initial_fuel" as_int
let (get_initial_ifuel : unit -> Prims.int) =
  fun uu___ -> lookup_opt "initial_ifuel" as_int
let (get_keep_query_captions : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "keep_query_captions" as_bool
let (get_lax : unit -> Prims.bool) = fun uu___ -> lookup_opt "lax" as_bool
let (get_load : unit -> Prims.string Prims.list) =
  fun uu___ -> lookup_opt "load" (as_list as_string)
let (get_load_cmxs : unit -> Prims.string Prims.list) =
  fun uu___ -> lookup_opt "load_cmxs" (as_list as_string)
let (get_log_queries : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "log_queries" as_bool
let (get_log_failing_queries : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "log_failing_queries" as_bool
let (get_log_types : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "log_types" as_bool
let (get_max_fuel : unit -> Prims.int) =
  fun uu___ -> lookup_opt "max_fuel" as_int
let (get_max_ifuel : unit -> Prims.int) =
  fun uu___ -> lookup_opt "max_ifuel" as_int
let (get_MLish : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "MLish" as_bool
let (get_MLish_effect : unit -> Prims.string) =
  fun uu___ -> lookup_opt "MLish_effect" as_string
let (get_no_default_includes : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "no_default_includes" as_bool
let (get_no_extract : unit -> Prims.string Prims.list) =
  fun uu___ -> lookup_opt "no_extract" (as_list as_string)
let (get_no_location_info : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "no_location_info" as_bool
let (get_no_plugins : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "no_plugins" as_bool
let (get_no_smt : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "no_smt" as_bool
let (get_normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "normalize_pure_terms_for_extraction" as_bool
let (get_krmloutput : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu___ -> lookup_opt "krmloutput" (as_option as_string)
let (get_odir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu___ -> lookup_opt "odir" (as_option as_string)
let (get_output_deps_to :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu___ -> lookup_opt "output_deps_to" (as_option as_string)
let (get_ugly : unit -> Prims.bool) = fun uu___ -> lookup_opt "ugly" as_bool
let (get_prims : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu___ -> lookup_opt "prims" (as_option as_string)
let (get_print_bound_var_types : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "print_bound_var_types" as_bool
let (get_print_effect_args : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "print_effect_args" as_bool
let (get_print_expected_failures : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "print_expected_failures" as_bool
let (get_print_full_names : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "print_full_names" as_bool
let (get_print_implicits : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "print_implicits" as_bool
let (get_print_universes : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "print_universes" as_bool
let (get_print_z3_statistics : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "print_z3_statistics" as_bool
let (get_prn : unit -> Prims.bool) = fun uu___ -> lookup_opt "prn" as_bool
let (get_proof_recovery : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "proof_recovery" as_bool
let (get_quake_lo : unit -> Prims.int) =
  fun uu___ -> lookup_opt "quake_lo" as_int
let (get_quake_hi : unit -> Prims.int) =
  fun uu___ -> lookup_opt "quake_hi" as_int
let (get_quake_keep : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "quake_keep" as_bool
let (get_query_cache : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "query_cache" as_bool
let (get_query_stats : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "query_stats" as_bool
let (get_read_checked_file :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu___ -> lookup_opt "read_checked_file" (as_option as_string)
let (get_read_krml_file :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu___ -> lookup_opt "read_krml_file" (as_option as_string)
let (get_list_plugins : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "list_plugins" as_bool
let (get_locate : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "locate" as_bool
let (get_locate_lib : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "locate_lib" as_bool
let (get_locate_ocaml : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "locate_ocaml" as_bool
let (get_record_hints : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "record_hints" as_bool
let (get_record_options : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "record_options" as_bool
let (get_retry : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "retry" as_bool
let (get_reuse_hint_for :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu___ -> lookup_opt "reuse_hint_for" (as_option as_string)
let (get_report_assumes :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu___ -> lookup_opt "report_assumes" (as_option as_string)
let (get_silent : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "silent" as_bool
let (get_smt : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu___ -> lookup_opt "smt" (as_option as_string)
let (get_smtencoding_elim_box : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "smtencoding.elim_box" as_bool
let (get_smtencoding_nl_arith_repr : unit -> Prims.string) =
  fun uu___ -> lookup_opt "smtencoding.nl_arith_repr" as_string
let (get_smtencoding_l_arith_repr : unit -> Prims.string) =
  fun uu___ -> lookup_opt "smtencoding.l_arith_repr" as_string
let (get_smtencoding_valid_intro : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "smtencoding.valid_intro" as_bool
let (get_smtencoding_valid_elim : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "smtencoding.valid_elim" as_bool
let (get_split_queries : unit -> Prims.string) =
  fun uu___ -> lookup_opt "split_queries" as_string
let (get_tactic_raw_binders : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "tactic_raw_binders" as_bool
let (get_tactics_failhard : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "tactics_failhard" as_bool
let (get_tactics_info : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "tactics_info" as_bool
let (get_tactic_trace : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "tactic_trace" as_bool
let (get_tactic_trace_d : unit -> Prims.int) =
  fun uu___ -> lookup_opt "tactic_trace_d" as_int
let (get_tactics_nbe : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "__tactics_nbe" as_bool
let (get_tcnorm : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "tcnorm" as_bool
let (get_timing : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "timing" as_bool
let (get_trace_error : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "trace_error" as_bool
let (get_unthrottle_inductives : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "unthrottle_inductives" as_bool
let (get_unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "unsafe_tactic_exec" as_bool
let (get_use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "use_eq_at_higher_order" as_bool
let (get_use_hints : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "use_hints" as_bool
let (get_use_hint_hashes : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "use_hint_hashes" as_bool
let (get_use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu___ -> lookup_opt "use_native_tactics" (as_option as_string)
let (get_no_tactics : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "no_tactics" as_bool
let (get_using_facts_from :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu___ -> lookup_opt "using_facts_from" (as_option (as_list as_string))
let (get_verify_module : unit -> Prims.string Prims.list) =
  fun uu___ -> lookup_opt "verify_module" (as_list as_string)
let (get_version : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "version" as_bool
let (get_warn_default_effects : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "warn_default_effects" as_bool
let (get_z3cliopt : unit -> Prims.string Prims.list) =
  fun uu___ -> lookup_opt "z3cliopt" (as_list as_string)
let (get_z3smtopt : unit -> Prims.string Prims.list) =
  fun uu___ -> lookup_opt "z3smtopt" (as_list as_string)
let (get_z3refresh : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "z3refresh" as_bool
let (get_z3rlimit : unit -> Prims.int) =
  fun uu___ -> lookup_opt "z3rlimit" as_int
let (get_z3rlimit_factor : unit -> Prims.int) =
  fun uu___ -> lookup_opt "z3rlimit_factor" as_int
let (get_z3seed : unit -> Prims.int) =
  fun uu___ -> lookup_opt "z3seed" as_int
let (get_z3version : unit -> Prims.string) =
  fun uu___ -> lookup_opt "z3version" as_string
let (get_no_positivity : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "__no_positivity" as_bool
let (get_warn_error : unit -> Prims.string Prims.list) =
  fun uu___ -> lookup_opt "warn_error" (as_list as_string)
let (get_use_nbe : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "use_nbe" as_bool
let (get_use_nbe_for_extraction : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "use_nbe_for_extraction" as_bool
let (get_trivial_pre_for_unannotated_effectful_fns : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "trivial_pre_for_unannotated_effectful_fns" as_bool
let (get_profile :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu___ -> lookup_opt "profile" (as_option (as_list as_string))
let (get_profile_group_by_decl : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "profile_group_by_decl" as_bool
let (get_profile_component :
  unit -> Prims.string Prims.list FStar_Pervasives_Native.option) =
  fun uu___ -> lookup_opt "profile_component" (as_option (as_list as_string))
let (_version : Prims.string FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Util.mk_ref ""
let (_platform : Prims.string FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Util.mk_ref ""
let (_compiler : Prims.string FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Util.mk_ref ""
let (_date : Prims.string FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Util.mk_ref " not set"
let (_commit : Prims.string FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Util.mk_ref ""
let (display_version : unit -> unit) =
  fun uu___ ->
    let uu___1 =
      let uu___2 = FStarC_Compiler_Effect.op_Bang _version in
      let uu___3 = FStarC_Compiler_Effect.op_Bang _platform in
      let uu___4 = FStarC_Compiler_Effect.op_Bang _compiler in
      let uu___5 = FStarC_Compiler_Effect.op_Bang _date in
      let uu___6 = FStarC_Compiler_Effect.op_Bang _commit in
      FStarC_Compiler_Util.format5
        "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n" uu___2 uu___3
        uu___4 uu___5 uu___6 in
    FStarC_Compiler_Util.print_string uu___1
let (display_debug_keys : unit -> unit) =
  fun uu___ ->
    let keys = FStarC_Compiler_Debug.list_all_toggles () in
    let uu___1 =
      FStarC_Compiler_List.sortWith FStarC_Compiler_String.compare keys in
    FStarC_Compiler_List.iter
      (fun s ->
         let uu___2 = FStarC_Compiler_String.op_Hat s "\n" in
         FStarC_Compiler_Util.print_string uu___2) uu___1
let (display_usage_aux :
  (FStarC_Getopt.opt * FStarC_Pprint.document) Prims.list -> unit) =
  fun specs ->
    let text s =
      let uu___ = FStarC_Pprint.break_ Prims.int_one in
      let uu___1 = FStarC_Pprint.words s in FStarC_Pprint.flow uu___ uu___1 in
    let bold_doc d =
      let uu___ =
        let uu___1 = FStarC_Compiler_Util.stdout_isatty () in
        uu___1 = (FStar_Pervasives_Native.Some true) in
      if uu___
      then
        let uu___1 = FStarC_Pprint.fancystring "\027[39;1m" Prims.int_zero in
        let uu___2 =
          let uu___3 = FStarC_Pprint.fancystring "\027[0m" Prims.int_zero in
          FStarC_Pprint.op_Hat_Hat d uu___3 in
        FStarC_Pprint.op_Hat_Hat uu___1 uu___2
      else d in
    let d =
      let uu___ =
        FStarC_Pprint.doc_of_string
          "fstar.exe [options] file[s] [@respfile...]" in
      let uu___1 =
        let uu___2 =
          let uu___3 =
            let uu___4 = FStarC_Compiler_Util.colorize_bold "@" in
            FStarC_Compiler_Util.format1
              "  %srespfile: read command-line options from respfile\n"
              uu___4 in
          FStarC_Pprint.doc_of_string uu___3 in
        let uu___3 =
          FStarC_Compiler_List.fold_right
            (fun uu___4 ->
               fun rest ->
                 match uu___4 with
                 | ((short, flag, p), explain) ->
                     let arg =
                       match p with
                       | FStarC_Getopt.ZeroArgs uu___5 -> FStarC_Pprint.empty
                       | FStarC_Getopt.OneArg (uu___5, argname) ->
                           let uu___6 = FStarC_Pprint.blank Prims.int_one in
                           let uu___7 = FStarC_Pprint.doc_of_string argname in
                           FStarC_Pprint.op_Hat_Hat uu___6 uu___7 in
                     let short_opt =
                       if short <> FStarC_Getopt.noshort
                       then
                         let uu___5 =
                           let uu___6 =
                             let uu___7 =
                               let uu___8 =
                                 FStarC_Compiler_String.make Prims.int_one
                                   short in
                               FStarC_Compiler_String.op_Hat "-" uu___8 in
                             FStarC_Pprint.doc_of_string uu___7 in
                           FStarC_Pprint.op_Hat_Hat uu___6 arg in
                         [uu___5]
                       else [] in
                     let long_opt =
                       if flag <> ""
                       then
                         let uu___5 =
                           let uu___6 =
                             let uu___7 =
                               FStarC_Compiler_String.op_Hat "--" flag in
                             FStarC_Pprint.doc_of_string uu___7 in
                           FStarC_Pprint.op_Hat_Hat uu___6 arg in
                         [uu___5]
                       else [] in
                     let uu___5 =
                       let uu___6 =
                         let uu___7 =
                           let uu___8 =
                             let uu___9 = FStarC_Pprint.blank Prims.int_one in
                             FStarC_Pprint.op_Hat_Hat FStarC_Pprint.comma
                               uu___9 in
                           FStarC_Pprint.separate uu___8
                             (FStarC_Compiler_List.op_At short_opt long_opt) in
                         bold_doc uu___7 in
                       FStarC_Pprint.group uu___6 in
                     let uu___6 =
                       let uu___7 =
                         let uu___8 =
                           let uu___9 =
                             let uu___10 =
                               FStarC_Pprint.blank (Prims.of_int (4)) in
                             let uu___11 = FStarC_Pprint.align explain in
                             FStarC_Pprint.op_Hat_Hat uu___10 uu___11 in
                           FStarC_Pprint.group uu___9 in
                         let uu___9 =
                           FStarC_Pprint.op_Hat_Hat FStarC_Pprint.hardline
                             rest in
                         FStarC_Pprint.op_Hat_Hat uu___8 uu___9 in
                       FStarC_Pprint.op_Hat_Hat FStarC_Pprint.hardline uu___7 in
                     FStarC_Pprint.op_Hat_Hat uu___5 uu___6) specs
            FStarC_Pprint.empty in
        FStarC_Pprint.op_Hat_Slash_Hat uu___2 uu___3 in
      FStarC_Pprint.op_Hat_Slash_Hat uu___ uu___1 in
    let uu___ =
      FStarC_Pprint.pretty_string
        (FStarC_Compiler_Util.float_of_string "1.0") (Prims.of_int (80)) d in
    FStarC_Compiler_Util.print_string uu___
let (mk_spec :
  (FStarC_BaseTypes.char * Prims.string * option_val
    FStarC_Getopt.opt_variant) -> FStarC_Getopt.opt)
  =
  fun o ->
    let uu___ = o in
    match uu___ with
    | (ns, name, arg) ->
        let arg1 =
          match arg with
          | FStarC_Getopt.ZeroArgs f ->
              let g uu___1 = let uu___2 = f () in set_option name uu___2 in
              FStarC_Getopt.ZeroArgs g
          | FStarC_Getopt.OneArg (f, d) ->
              let g x = let uu___1 = f x in set_option name uu___1 in
              FStarC_Getopt.OneArg (g, d) in
        (ns, name, arg1)
let (accumulated_option : Prims.string -> option_val -> option_val) =
  fun name ->
    fun value ->
      let prev_values =
        let uu___ = lookup_opt name (as_option as_list') in
        FStarC_Compiler_Util.dflt [] uu___ in
      List (value :: prev_values)
let (reverse_accumulated_option : Prims.string -> option_val -> option_val) =
  fun name ->
    fun value ->
      let prev_values =
        let uu___ = lookup_opt name (as_option as_list') in
        FStarC_Compiler_Util.dflt [] uu___ in
      List (FStarC_Compiler_List.op_At prev_values [value])
let accumulate_string :
  'uuuuu . Prims.string -> ('uuuuu -> Prims.string) -> 'uuuuu -> unit =
  fun name ->
    fun post_processor ->
      fun value ->
        let uu___ =
          let uu___1 = let uu___2 = post_processor value in String uu___2 in
          accumulated_option name uu___1 in
        set_option name uu___
let (add_extract_module : Prims.string -> unit) =
  fun s ->
    accumulate_string "extract_module" FStarC_Compiler_String.lowercase s
let (add_extract_namespace : Prims.string -> unit) =
  fun s ->
    accumulate_string "extract_namespace" FStarC_Compiler_String.lowercase s
let (add_verify_module : Prims.string -> unit) =
  fun s ->
    accumulate_string "verify_module" FStarC_Compiler_String.lowercase s
exception InvalidArgument of Prims.string 
let (uu___is_InvalidArgument : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | InvalidArgument uu___ -> true | uu___ -> false
let (__proj__InvalidArgument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee -> match projectee with | InvalidArgument uu___ -> uu___
let rec (parse_opt_val :
  Prims.string -> opt_type -> Prims.string -> option_val) =
  fun opt_name ->
    fun typ ->
      fun str_val ->
        try
          (fun uu___ ->
             match () with
             | () ->
                 (match typ with
                  | Const c -> c
                  | IntStr uu___1 ->
                      let uu___2 =
                        FStarC_Compiler_Util.safe_int_of_string str_val in
                      (match uu___2 with
                       | FStar_Pervasives_Native.Some v -> Int v
                       | FStar_Pervasives_Native.None ->
                           FStarC_Compiler_Effect.raise
                             (InvalidArgument opt_name))
                  | BoolStr ->
                      let uu___1 =
                        if str_val = "true"
                        then true
                        else
                          if str_val = "false"
                          then false
                          else
                            FStarC_Compiler_Effect.raise
                              (InvalidArgument opt_name) in
                      Bool uu___1
                  | PathStr uu___1 -> Path str_val
                  | SimpleStr uu___1 -> String str_val
                  | EnumStr strs ->
                      if FStarC_Compiler_List.mem str_val strs
                      then String str_val
                      else
                        FStarC_Compiler_Effect.raise
                          (InvalidArgument opt_name)
                  | OpenEnumStr uu___1 -> String str_val
                  | PostProcessed (pp, elem_spec) ->
                      let uu___1 = parse_opt_val opt_name elem_spec str_val in
                      pp uu___1
                  | Accumulated elem_spec ->
                      let v = parse_opt_val opt_name elem_spec str_val in
                      accumulated_option opt_name v
                  | ReverseAccumulated elem_spec ->
                      let v = parse_opt_val opt_name elem_spec str_val in
                      reverse_accumulated_option opt_name v
                  | WithSideEffect (side_effect, elem_spec) ->
                      (side_effect ();
                       parse_opt_val opt_name elem_spec str_val))) ()
        with
        | InvalidArgument opt_name1 ->
            let uu___1 =
              FStarC_Compiler_Util.format1 "Invalid argument to --%s"
                opt_name1 in
            failwith uu___1
let rec (desc_of_opt_type :
  opt_type -> Prims.string FStar_Pervasives_Native.option) =
  fun typ ->
    let desc_of_enum cases =
      FStar_Pervasives_Native.Some (FStarC_Compiler_String.concat "|" cases) in
    match typ with
    | Const c -> FStar_Pervasives_Native.None
    | IntStr desc -> FStar_Pervasives_Native.Some desc
    | BoolStr -> desc_of_enum ["true"; "false"]
    | PathStr desc -> FStar_Pervasives_Native.Some desc
    | SimpleStr desc -> FStar_Pervasives_Native.Some desc
    | EnumStr strs -> desc_of_enum strs
    | OpenEnumStr (strs, desc) ->
        desc_of_enum (FStarC_Compiler_List.op_At strs [desc])
    | PostProcessed (uu___, elem_spec) -> desc_of_opt_type elem_spec
    | Accumulated elem_spec -> desc_of_opt_type elem_spec
    | ReverseAccumulated elem_spec -> desc_of_opt_type elem_spec
    | WithSideEffect (uu___, elem_spec) -> desc_of_opt_type elem_spec
let (arg_spec_of_opt_type :
  Prims.string -> opt_type -> option_val FStarC_Getopt.opt_variant) =
  fun opt_name ->
    fun typ ->
      let wrap s =
        let uu___ = FStarC_Compiler_String.op_Hat s ">" in
        FStarC_Compiler_String.op_Hat "<" uu___ in
      let parser = parse_opt_val opt_name typ in
      let uu___ = desc_of_opt_type typ in
      match uu___ with
      | FStar_Pervasives_Native.None ->
          FStarC_Getopt.ZeroArgs ((fun uu___1 -> parser ""))
      | FStar_Pervasives_Native.Some desc ->
          let desc1 = wrap desc in FStarC_Getopt.OneArg (parser, desc1)
let (pp_validate_dir : option_val -> option_val) =
  fun p ->
    let pp = as_string p in FStarC_Compiler_Util.mkdir false true pp; p
let (pp_lowercase : option_val -> option_val) =
  fun s ->
    let uu___ =
      let uu___1 = as_string s in FStarC_Compiler_String.lowercase uu___1 in
    String uu___
let (abort_counter : Prims.int FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Util.mk_ref Prims.int_zero
let (interp_quake_arg : Prims.string -> (Prims.int * Prims.int * Prims.bool))
  =
  fun s ->
    let ios = FStarC_Compiler_Util.int_of_string in
    match FStarC_Compiler_Util.split s "/" with
    | f::[] ->
        let uu___ = ios f in let uu___1 = ios f in (uu___, uu___1, false)
    | f1::f2::[] ->
        if f2 = "k"
        then
          let uu___ = ios f1 in let uu___1 = ios f1 in (uu___, uu___1, true)
        else
          (let uu___1 = ios f1 in
           let uu___2 = ios f2 in (uu___1, uu___2, false))
    | f1::f2::k::[] ->
        if k = "k"
        then
          let uu___ = ios f1 in let uu___1 = ios f2 in (uu___, uu___1, true)
        else failwith "unexpected value for --quake"
    | uu___ -> failwith "unexpected value for --quake"
let (uu___1 : (((Prims.string -> unit) -> unit) * (Prims.string -> unit))) =
  let cb = FStarC_Compiler_Util.mk_ref FStar_Pervasives_Native.None in
  let set1 f =
    FStarC_Compiler_Effect.op_Colon_Equals cb
      (FStar_Pervasives_Native.Some f) in
  let call msg =
    let uu___ = FStarC_Compiler_Effect.op_Bang cb in
    match uu___ with
    | FStar_Pervasives_Native.None -> ()
    | FStar_Pervasives_Native.Some f -> f msg in
  (set1, call)
let (set_option_warning_callback_aux : (Prims.string -> unit) -> unit) =
  match uu___1 with
  | (set_option_warning_callback_aux1, option_warning_callback) ->
      set_option_warning_callback_aux1
let (option_warning_callback : Prims.string -> unit) =
  match uu___1 with
  | (set_option_warning_callback_aux1, option_warning_callback1) ->
      option_warning_callback1
let (set_option_warning_callback : (Prims.string -> unit) -> unit) =
  fun f -> set_option_warning_callback_aux f
let rec (specs_with_types :
  Prims.bool ->
    (FStarC_BaseTypes.char * Prims.string * opt_type *
      FStarC_Pprint.document) Prims.list)
  =
  fun warn_unsafe ->
    let text s =
      let uu___ = FStarC_Pprint.break_ Prims.int_one in
      let uu___2 = FStarC_Pprint.words s in FStarC_Pprint.flow uu___ uu___2 in
    let uu___ =
      let uu___2 =
        text
          "Abort on the n-th error or warning raised. Useful in combination with --trace_error. Count starts at 1, use 0 to disable. (default 0)" in
      (FStarC_Getopt.noshort, "abort_on",
        (PostProcessed
           ((fun uu___3 ->
               match uu___3 with
               | Int x ->
                   (FStarC_Compiler_Effect.op_Colon_Equals abort_counter x;
                    Int x)
               | x -> failwith "?"), (IntStr "non-negative integer"))),
        uu___2) in
    let uu___2 =
      let uu___3 =
        let uu___4 = text "Admit SMT queries, unsafe! (default 'false')" in
        (FStarC_Getopt.noshort, "admit_smt_queries",
          (WithSideEffect
             ((fun uu___5 ->
                 if warn_unsafe
                 then option_warning_callback "admit_smt_queries"
                 else ()), BoolStr)), uu___4) in
      let uu___4 =
        let uu___5 =
          let uu___6 =
            text
              "Admit all queries, except those with label ( symbol,  id))(e.g. --admit_except '(FStar.Fin.pigeonhole, 1)' or --admit_except FStar.Fin.pigeonhole)" in
          (FStarC_Getopt.noshort, "admit_except",
            (WithSideEffect
               ((fun uu___7 ->
                   if warn_unsafe
                   then option_warning_callback "admit_except"
                   else ()), (SimpleStr "[symbol|(symbol, id)]"))), uu___6) in
        let uu___6 =
          let uu___7 =
            let uu___8 =
              text
                "Retain behavior of the tactic engine prior to the introduction of FStarC.TypeChecker.Core (0 is most permissive, 2 is least permissive)" in
            (FStarC_Getopt.noshort, "compat_pre_core", (IntStr "0, 1, 2"),
              uu___8) in
          let uu___8 =
            let uu___9 =
              let uu___10 = text "Retain untyped indexed effects implicits" in
              (FStarC_Getopt.noshort, "compat_pre_typed_indexed_effects",
                (Const (Bool true)), uu___10) in
            let uu___10 =
              let uu___11 =
                let uu___12 =
                  text
                    "Fail if the SMT guard are produced when the tactic engine re-checks solutions produced by the unifier (default 'false')" in
                (FStarC_Getopt.noshort, "disallow_unification_guards",
                  BoolStr, uu___12) in
              let uu___12 =
                let uu___13 =
                  let uu___14 =
                    text
                      "Expects all modules whose names or namespaces match the provided options to already have valid .checked files in the include path" in
                  (FStarC_Getopt.noshort, "already_cached",
                    (Accumulated
                       (SimpleStr
                          "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
                    uu___14) in
                let uu___14 =
                  let uu___15 =
                    let uu___16 =
                      text
                        "Write a '.checked' file for each module after verification and read from it if present, instead of re-verifying" in
                    (FStarC_Getopt.noshort, "cache_checked_modules",
                      (Const (Bool true)), uu___16) in
                  let uu___16 =
                    let uu___17 =
                      let uu___18 =
                        text
                          "Read and write .checked and .checked.lax in directory dir" in
                      (FStarC_Getopt.noshort, "cache_dir",
                        (PostProcessed (pp_validate_dir, (PathStr "dir"))),
                        uu___18) in
                    let uu___18 =
                      let uu___19 =
                        let uu___20 =
                          text "Do not read or write any .checked files" in
                        (FStarC_Getopt.noshort, "cache_off",
                          (Const (Bool true)), uu___20) in
                      let uu___20 =
                        let uu___21 =
                          let uu___22 =
                            text
                              "Print the version for .checked files and exit." in
                          (FStarC_Getopt.noshort, "print_cache_version",
                            (Const (Bool true)), uu___22) in
                        let uu___22 =
                          let uu___23 =
                            let uu___24 =
                              text
                                "Inline across module interfaces during extraction (aka. cross-module inlining)" in
                            (FStarC_Getopt.noshort, "cmi",
                              (Const (Bool true)), uu___24) in
                          let uu___24 =
                            let uu___25 =
                              let uu___26 =
                                text
                                  "Generate code for further compilation to executable code, or build a compiler plugin" in
                              (FStarC_Getopt.noshort, "codegen",
                                (EnumStr
                                   ["OCaml";
                                   "FSharp";
                                   "krml";
                                   "Plugin";
                                   "Extension"]), uu___26) in
                            let uu___26 =
                              let uu___27 =
                                let uu___28 =
                                  text
                                    "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)" in
                                (FStarC_Getopt.noshort, "codegen-lib",
                                  (Accumulated (SimpleStr "namespace")),
                                  uu___28) in
                              let uu___28 =
                                let uu___29 =
                                  let uu___30 =
                                    text
                                      "Enable general debugging, i.e. increase verbosity." in
                                  (100, "",
                                    (PostProcessed
                                       ((fun o ->
                                           FStarC_Compiler_Debug.enable (); o),
                                         (Const (Bool true)))), uu___30) in
                                let uu___30 =
                                  let uu___31 =
                                    let uu___32 =
                                      text
                                        "Enable specific debug toggles (comma-separated list of debug keys)" in
                                    (FStarC_Getopt.noshort, "debug",
                                      (PostProcessed
                                         ((fun o ->
                                             let keys =
                                               as_comma_string_list o in
                                             FStarC_Compiler_Debug.enable_toggles
                                               keys;
                                             o),
                                           (ReverseAccumulated
                                              (SimpleStr "debug toggles")))),
                                      uu___32) in
                                  let uu___32 =
                                    let uu___33 =
                                      let uu___34 =
                                        text
                                          "Enable all debug toggles. WARNING: this will cause a lot of output!" in
                                      (FStarC_Getopt.noshort, "debug_all",
                                        (PostProcessed
                                           ((fun o ->
                                               match o with
                                               | Bool (true) ->
                                                   (FStarC_Compiler_Debug.set_debug_all
                                                      ();
                                                    o)
                                               | uu___35 -> failwith "?"),
                                             (Const (Bool true)))), uu___34) in
                                    let uu___34 =
                                      let uu___35 =
                                        let uu___36 =
                                          text
                                            "Enable to make the effect of --debug apply to every module processed by the compiler, including dependencies." in
                                        (FStarC_Getopt.noshort,
                                          "debug_all_modules",
                                          (Const (Bool true)), uu___36) in
                                      let uu___36 =
                                        let uu___37 =
                                          let uu___38 =
                                            let uu___39 =
                                              text
                                                "Enable several internal sanity checks, useful to track bugs and report issues." in
                                            let uu___40 =
                                              let uu___41 =
                                                let uu___42 =
                                                  let uu___43 =
                                                    text
                                                      "if 'no', no checks are performed" in
                                                  let uu___44 =
                                                    let uu___45 =
                                                      text
                                                        "if 'warn', checks are performed and raise a warning when they fail" in
                                                    let uu___46 =
                                                      let uu___47 =
                                                        text
                                                          "if 'error, like 'warn', but the compiler raises a hard error instead" in
                                                      let uu___48 =
                                                        let uu___49 =
                                                          text
                                                            "if 'abort, like 'warn', but the compiler immediately aborts on an error" in
                                                        [uu___49] in
                                                      uu___47 :: uu___48 in
                                                    uu___45 :: uu___46 in
                                                  uu___43 :: uu___44 in
                                                FStarC_Errors_Msg.bulleted
                                                  uu___42 in
                                              let uu___42 =
                                                text "(default 'no')" in
                                              FStarC_Pprint.op_Hat_Slash_Hat
                                                uu___41 uu___42 in
                                            FStarC_Pprint.op_Hat_Hat uu___39
                                              uu___40 in
                                          (FStarC_Getopt.noshort,
                                            "defensive",
                                            (EnumStr
                                               ["no";
                                               "warn";
                                               "error";
                                               "abort"]), uu___38) in
                                        let uu___38 =
                                          let uu___39 =
                                            let uu___40 =
                                              let uu___41 =
                                                text
                                                  "Output the transitive closure of the full dependency graph in three formats:" in
                                              let uu___42 =
                                                let uu___43 =
                                                  let uu___44 =
                                                    text
                                                      "'graph': a format suitable the 'dot' tool from 'GraphViz'" in
                                                  let uu___45 =
                                                    let uu___46 =
                                                      text
                                                        "'full': a format suitable for 'make', including dependences for producing .ml and .krml files" in
                                                    let uu___47 =
                                                      let uu___48 =
                                                        text
                                                          "'make': (deprecated) a format suitable for 'make', including only dependences among source files" in
                                                      [uu___48] in
                                                    uu___46 :: uu___47 in
                                                  uu___44 :: uu___45 in
                                                FStarC_Errors_Msg.bulleted
                                                  uu___43 in
                                              FStarC_Pprint.op_Hat_Hat
                                                uu___41 uu___42 in
                                            (FStarC_Getopt.noshort, "dep",
                                              (EnumStr
                                                 ["make";
                                                 "graph";
                                                 "full";
                                                 "raw"]), uu___40) in
                                          let uu___40 =
                                            let uu___41 =
                                              let uu___42 =
                                                text
                                                  "Emit a detailed error report by asking the SMT solver many queries; will take longer" in
                                              (FStarC_Getopt.noshort,
                                                "detail_errors",
                                                (Const (Bool true)), uu___42) in
                                            let uu___42 =
                                              let uu___43 =
                                                let uu___44 =
                                                  text
                                                    "Emit a detailed report for proof whose unsat core fails to replay" in
                                                (FStarC_Getopt.noshort,
                                                  "detail_hint_replay",
                                                  (Const (Bool true)),
                                                  uu___44) in
                                              let uu___44 =
                                                let uu___45 =
                                                  let uu___46 =
                                                    text
                                                      "Print out this module as it passes through the compiler pipeline" in
                                                  (FStarC_Getopt.noshort,
                                                    "dump_module",
                                                    (Accumulated
                                                       (SimpleStr
                                                          "module_name")),
                                                    uu___46) in
                                                let uu___46 =
                                                  let uu___47 =
                                                    let uu___48 =
                                                      text
                                                        "Try to solve subtyping constraints at each binder (loses precision but may be slightly more efficient)" in
                                                    (FStarC_Getopt.noshort,
                                                      "eager_subtyping",
                                                      (Const (Bool true)),
                                                      uu___48) in
                                                  let uu___48 =
                                                    let uu___49 =
                                                      let uu___50 =
                                                        text
                                                          "Print context information for each error or warning raised (default false)" in
                                                      (FStarC_Getopt.noshort,
                                                        "error_contexts",
                                                        BoolStr, uu___50) in
                                                    let uu___50 =
                                                      let uu___51 =
                                                        let uu___52 =
                                                          text
                                                            "These options are set in extensions option map. Keys are usually namespaces separated by \":\". E.g., 'pulse:verbose=1;my:extension:option=xyz;foo:bar=baz'. These options are typically interpreted by extensions. Any later use of --ext over the same key overrides the old value. An entry 'e' that is not of the form 'a=b' is treated as 'e=1', i.e., 'e' associated with string \"1\"." in
                                                        (FStarC_Getopt.noshort,
                                                          "ext",
                                                          (PostProcessed
                                                             ((fun o ->
                                                                 let parse_ext
                                                                   s =
                                                                   let exts =
                                                                    FStarC_Compiler_Util.split
                                                                    s ";" in
                                                                   FStarC_Compiler_List.collect
                                                                    (fun s1
                                                                    ->
                                                                    match 
                                                                    FStarC_Compiler_Util.split
                                                                    s1 "="
                                                                    with
                                                                    | 
                                                                    k::v::[]
                                                                    ->
                                                                    [(k, v)]
                                                                    | 
                                                                    uu___53
                                                                    ->
                                                                    [
                                                                    (s1, "1")])
                                                                    exts in
                                                                 (let uu___54
                                                                    =
                                                                    let uu___55
                                                                    =
                                                                    as_comma_string_list
                                                                    o in
                                                                    FStarC_Compiler_List.collect
                                                                    parse_ext
                                                                    uu___55 in
                                                                  FStarC_Compiler_List.iter
                                                                    (
                                                                    fun
                                                                    uu___55
                                                                    ->
                                                                    match uu___55
                                                                    with
                                                                    | 
                                                                    (k, v) ->
                                                                    FStarC_Options_Ext.set
                                                                    k v)
                                                                    uu___54);
                                                                 o),
                                                               (ReverseAccumulated
                                                                  (SimpleStr
                                                                    "extension knobs")))),
                                                          uu___52) in
                                                      let uu___52 =
                                                        let uu___53 =
                                                          let uu___54 =
                                                            text
                                                              "Extract only those modules whose names or namespaces match the provided options. 'TargetName' ranges over {OCaml, krml, FSharp, Plugin, Extension}. A 'ModuleSelector' is a space or comma-separated list of '[+|-]( * | namespace | module)'. For example --extract 'OCaml:A -A.B' --extract 'krml:A -A.C' --extract '*' means for OCaml, extract everything in the A namespace only except A.B; for krml, extract everything in the A namespace only except A.C; for everything else, extract everything. Note, the '+' is optional: --extract '+A' and --extract 'A' mean the same thing. Note also that '--extract A' applies both to a module named 'A' and to any module in the 'A' namespace Multiple uses of this option accumulate, e.g., --extract A --extract B is interpreted as --extract 'A B'." in
                                                          (FStarC_Getopt.noshort,
                                                            "extract",
                                                            (Accumulated
                                                               (SimpleStr
                                                                  "One or more semicolon separated occurrences of '[TargetName:]ModuleSelector'")),
                                                            uu___54) in
                                                        let uu___54 =
                                                          let uu___55 =
                                                            let uu___56 =
                                                              text
                                                                "Deprecated: use --extract instead; Only extract the specified modules (instead of the possibly-partial dependency graph)" in
                                                            (FStarC_Getopt.noshort,
                                                              "extract_module",
                                                              (Accumulated
                                                                 (PostProcessed
                                                                    (pp_lowercase,
                                                                    (SimpleStr
                                                                    "module_name")))),
                                                              uu___56) in
                                                          let uu___56 =
                                                            let uu___57 =
                                                              let uu___58 =
                                                                text
                                                                  "Deprecated: use --extract instead; Only extract modules in the specified namespace" in
                                                              (FStarC_Getopt.noshort,
                                                                "extract_namespace",
                                                                (Accumulated
                                                                   (PostProcessed
                                                                    (pp_lowercase,
                                                                    (SimpleStr
                                                                    "namespace name")))),
                                                                uu___58) in
                                                            let uu___58 =
                                                              let uu___59 =
                                                                let uu___60 =
                                                                  text
                                                                    "Explicitly break the abstraction imposed by the interface of any implementation file that appears on the command line (use with care!)" in
                                                                (FStarC_Getopt.noshort,
                                                                  "expose_interfaces",
                                                                  (Const
                                                                    (Bool
                                                                    true)),
                                                                  uu___60) in
                                                              let uu___60 =
                                                                let uu___61 =
                                                                  let uu___62
                                                                    =
                                                                    text
                                                                    "Format of the messages emitted by F* (default `human`)" in
                                                                  (FStarC_Getopt.noshort,
                                                                    "message_format",
                                                                    (
                                                                    EnumStr
                                                                    ["human";
                                                                    "json"]),
                                                                    uu___62) in
                                                                let uu___62 =
                                                                  let uu___63
                                                                    =
                                                                    let uu___64
                                                                    =
                                                                    text
                                                                    "Don't print unification variable numbers" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "hide_uvar_nums",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    uu___64) in
                                                                  let uu___64
                                                                    =
                                                                    let uu___65
                                                                    =
                                                                    let uu___66
                                                                    =
                                                                    text
                                                                    "Read/write hints to  dir/module_name.hints (instead of placing hint-file alongside source file)" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "hint_dir",
                                                                    (PostProcessed
                                                                    (pp_validate_dir,
                                                                    (PathStr
                                                                    "dir"))),
                                                                    uu___66) in
                                                                    let uu___66
                                                                    =
                                                                    let uu___67
                                                                    =
                                                                    let uu___68
                                                                    =
                                                                    text
                                                                    "Read/write hints to  path (instead of module-specific hints files; overrides hint_dir)" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "hint_file",
                                                                    (PathStr
                                                                    "path"),
                                                                    uu___68) in
                                                                    let uu___68
                                                                    =
                                                                    let uu___69
                                                                    =
                                                                    let uu___70
                                                                    =
                                                                    text
                                                                    "Print information regarding hints (deprecated; use --query_stats instead)" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "hint_info",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    uu___70) in
                                                                    let uu___70
                                                                    =
                                                                    let uu___71
                                                                    =
                                                                    let uu___72
                                                                    =
                                                                    text
                                                                    "Legacy interactive mode; reads input from stdin" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "in",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    uu___72) in
                                                                    let uu___72
                                                                    =
                                                                    let uu___73
                                                                    =
                                                                    let uu___74
                                                                    =
                                                                    text
                                                                    "JSON-based interactive mode for IDEs" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "ide",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    uu___74) in
                                                                    let uu___74
                                                                    =
                                                                    let uu___75
                                                                    =
                                                                    let uu___76
                                                                    =
                                                                    text
                                                                    "Disable identifier tables in IDE mode (temporary workaround useful in Steel)" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "ide_id_info_off",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    uu___76) in
                                                                    let uu___76
                                                                    =
                                                                    let uu___77
                                                                    =
                                                                    let uu___78
                                                                    =
                                                                    text
                                                                    "Language Server Protocol-based interactive mode for IDEs" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "lsp",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    uu___78) in
                                                                    let uu___78
                                                                    =
                                                                    let uu___79
                                                                    =
                                                                    let uu___80
                                                                    =
                                                                    text
                                                                    "A directory in which to search for files included on the command line" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "include",
                                                                    (ReverseAccumulated
                                                                    (PathStr
                                                                    "path")),
                                                                    uu___80) in
                                                                    let uu___80
                                                                    =
                                                                    let uu___81
                                                                    =
                                                                    let uu___82
                                                                    =
                                                                    text
                                                                    "Parses and prettyprints the files included on the command line" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "print",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    uu___82) in
                                                                    let uu___82
                                                                    =
                                                                    let uu___83
                                                                    =
                                                                    let uu___84
                                                                    =
                                                                    text
                                                                    "Parses and prettyprints in place the files included on the command line" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "print_in_place",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    uu___84) in
                                                                    let uu___84
                                                                    =
                                                                    let uu___85
                                                                    =
                                                                    let uu___86
                                                                    =
                                                                    text
                                                                    "Force checking the files given as arguments even if they have valid checked files" in
                                                                    (102,
                                                                    "force",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    uu___86) in
                                                                    let uu___86
                                                                    =
                                                                    let uu___87
                                                                    =
                                                                    let uu___88
                                                                    =
                                                                    text
                                                                    "Set initial_fuel and max_fuel at once" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "fuel",
                                                                    (PostProcessed
                                                                    ((fun
                                                                    uu___89
                                                                    ->
                                                                    match uu___89
                                                                    with
                                                                    | 
                                                                    String s
                                                                    ->
                                                                    let p f =
                                                                    let uu___90
                                                                    =
                                                                    FStarC_Compiler_Util.int_of_string
                                                                    f in
                                                                    Int
                                                                    uu___90 in
                                                                    let uu___90
                                                                    =
                                                                    match 
                                                                    FStarC_Compiler_Util.split
                                                                    s ","
                                                                    with
                                                                    | 
                                                                    f::[] ->
                                                                    (f, f)
                                                                    | 
                                                                    f1::f2::[]
                                                                    ->
                                                                    (f1, f2)
                                                                    | 
                                                                    uu___91
                                                                    ->
                                                                    failwith
                                                                    "unexpected value for --fuel" in
                                                                    (match uu___90
                                                                    with
                                                                    | 
                                                                    (min,
                                                                    max) ->
                                                                    ((
                                                                    let uu___92
                                                                    = p min in
                                                                    set_option
                                                                    "initial_fuel"
                                                                    uu___92);
                                                                    (let uu___93
                                                                    = p max in
                                                                    set_option
                                                                    "max_fuel"
                                                                    uu___93);
                                                                    String s))
                                                                    | 
                                                                    uu___90
                                                                    ->
                                                                    failwith
                                                                    "impos"),
                                                                    (SimpleStr
                                                                    "non-negative integer or pair of non-negative integers"))),
                                                                    uu___88) in
                                                                    let uu___88
                                                                    =
                                                                    let uu___89
                                                                    =
                                                                    let uu___90
                                                                    =
                                                                    text
                                                                    "Set initial_ifuel and max_ifuel at once" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "ifuel",
                                                                    (PostProcessed
                                                                    ((fun
                                                                    uu___91
                                                                    ->
                                                                    match uu___91
                                                                    with
                                                                    | 
                                                                    String s
                                                                    ->
                                                                    let p f =
                                                                    let uu___92
                                                                    =
                                                                    FStarC_Compiler_Util.int_of_string
                                                                    f in
                                                                    Int
                                                                    uu___92 in
                                                                    let uu___92
                                                                    =
                                                                    match 
                                                                    FStarC_Compiler_Util.split
                                                                    s ","
                                                                    with
                                                                    | 
                                                                    f::[] ->
                                                                    (f, f)
                                                                    | 
                                                                    f1::f2::[]
                                                                    ->
                                                                    (f1, f2)
                                                                    | 
                                                                    uu___93
                                                                    ->
                                                                    failwith
                                                                    "unexpected value for --ifuel" in
                                                                    (match uu___92
                                                                    with
                                                                    | 
                                                                    (min,
                                                                    max) ->
                                                                    ((
                                                                    let uu___94
                                                                    = p min in
                                                                    set_option
                                                                    "initial_ifuel"
                                                                    uu___94);
                                                                    (let uu___95
                                                                    = p max in
                                                                    set_option
                                                                    "max_ifuel"
                                                                    uu___95);
                                                                    String s))
                                                                    | 
                                                                    uu___92
                                                                    ->
                                                                    failwith
                                                                    "impos"),
                                                                    (SimpleStr
                                                                    "non-negative integer or pair of non-negative integers"))),
                                                                    uu___90) in
                                                                    let uu___90
                                                                    =
                                                                    let uu___91
                                                                    =
                                                                    let uu___92
                                                                    =
                                                                    text
                                                                    "Number of unrolling of recursive functions to try initially (default 2)" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "initial_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    uu___92) in
                                                                    let uu___92
                                                                    =
                                                                    let uu___93
                                                                    =
                                                                    let uu___94
                                                                    =
                                                                    text
                                                                    "Number of unrolling of inductive datatypes to try at first (default 1)" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "initial_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    uu___94) in
                                                                    let uu___94
                                                                    =
                                                                    let uu___95
                                                                    =
                                                                    let uu___96
                                                                    =
                                                                    text
                                                                    "Retain comments in the logged SMT queries (requires --log_queries or --log_failing_queries; default true)" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "keep_query_captions",
                                                                    BoolStr,
                                                                    uu___96) in
                                                                    let uu___96
                                                                    =
                                                                    let uu___97
                                                                    =
                                                                    let uu___98
                                                                    =
                                                                    text
                                                                    "Run the lax-type checker only (admit all verification conditions)" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "lax",
                                                                    (WithSideEffect
                                                                    ((fun
                                                                    uu___99
                                                                    ->
                                                                    if
                                                                    warn_unsafe
                                                                    then
                                                                    option_warning_callback
                                                                    "lax"
                                                                    else ()),
                                                                    (Const
                                                                    (Bool
                                                                    true)))),
                                                                    uu___98) in
                                                                    let uu___98
                                                                    =
                                                                    let uu___99
                                                                    =
                                                                    let uu___100
                                                                    =
                                                                    text
                                                                    "Load OCaml module, compiling it if necessary" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "load",
                                                                    (ReverseAccumulated
                                                                    (PathStr
                                                                    "module")),
                                                                    uu___100) in
                                                                    let uu___100
                                                                    =
                                                                    let uu___101
                                                                    =
                                                                    let uu___102
                                                                    =
                                                                    text
                                                                    "Load compiled module, fails hard if the module is not already compiled" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "load_cmxs",
                                                                    (ReverseAccumulated
                                                                    (PathStr
                                                                    "module")),
                                                                    uu___102) in
                                                                    let uu___102
                                                                    =
                                                                    let uu___103
                                                                    =
                                                                    let uu___104
                                                                    =
                                                                    text
                                                                    "Print types computed for data/val/let-bindings" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "log_types",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    uu___104) in
                                                                    let uu___104
                                                                    =
                                                                    let uu___105
                                                                    =
                                                                    let uu___106
                                                                    =
                                                                    text
                                                                    "Log the Z3 queries in several queries-*.smt2 files, as we go" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "log_queries",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    uu___106) in
                                                                    let uu___106
                                                                    =
                                                                    let uu___107
                                                                    =
                                                                    let uu___108
                                                                    =
                                                                    text
                                                                    "As --log_queries, but only save the failing queries. Each query is\n    saved in its own file regardless of whether they were checked during the\n    same invocation. The SMT2 file names begin with \"failedQueries\"" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "log_failing_queries",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    uu___108) in
                                                                    let uu___108
                                                                    =
                                                                    let uu___109
                                                                    =
                                                                    let uu___110
                                                                    =
                                                                    text
                                                                    "Number of unrolling of recursive functions to try at most (default 8)" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "max_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    uu___110) in
                                                                    let uu___110
                                                                    =
                                                                    let uu___111
                                                                    =
                                                                    let uu___112
                                                                    =
                                                                    text
                                                                    "Number of unrolling of inductive datatypes to try at most (default 2)" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "max_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    uu___112) in
                                                                    let uu___112
                                                                    =
                                                                    let uu___113
                                                                    =
                                                                    let uu___114
                                                                    =
                                                                    text
                                                                    "Trigger various specializations for compiling the F* compiler itself (not meant for user code)" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "MLish",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    uu___114) in
                                                                    let uu___114
                                                                    =
                                                                    let uu___115
                                                                    =
                                                                    let uu___116
                                                                    =
                                                                    text
                                                                    "Set the default effect *module* for --MLish (default: FStar.Compiler.Effect)" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "MLish_effect",
                                                                    (SimpleStr
                                                                    "module_name"),
                                                                    uu___116) in
                                                                    let uu___116
                                                                    =
                                                                    let uu___117
                                                                    =
                                                                    let uu___118
                                                                    =
                                                                    text
                                                                    "Ignore the default module search paths" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "no_default_includes",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    uu___118) in
                                                                    let uu___118
                                                                    =
                                                                    let uu___119
                                                                    =
                                                                    let uu___120
                                                                    =
                                                                    text
                                                                    "Deprecated: use --extract instead; Do not extract code from this module" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "no_extract",
                                                                    (Accumulated
                                                                    (PathStr
                                                                    "module name")),
                                                                    uu___120) in
                                                                    let uu___120
                                                                    =
                                                                    let uu___121
                                                                    =
                                                                    let uu___122
                                                                    =
                                                                    text
                                                                    "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "no_location_info",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    uu___122) in
                                                                    let uu___122
                                                                    =
                                                                    let uu___123
                                                                    =
                                                                    let uu___124
                                                                    =
                                                                    text
                                                                    "Do not send any queries to the SMT solver, and fail on them instead" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "no_smt",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    uu___124) in
                                                                    let uu___124
                                                                    =
                                                                    let uu___125
                                                                    =
                                                                    let uu___126
                                                                    =
                                                                    text
                                                                    "Extract top-level pure terms after normalizing them. This can lead to very large code, but can result in more partial evaluation and compile-time specialization." in
                                                                    (FStarC_Getopt.noshort,
                                                                    "normalize_pure_terms_for_extraction",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    uu___126) in
                                                                    let uu___126
                                                                    =
                                                                    let uu___127
                                                                    =
                                                                    let uu___128
                                                                    =
                                                                    text
                                                                    "Place KaRaMeL extraction output in file <filename>. The path can be relative or absolute and does not dependon the --odir option." in
                                                                    (FStarC_Getopt.noshort,
                                                                    "krmloutput",
                                                                    (PathStr
                                                                    "filename"),
                                                                    uu___128) in
                                                                    let uu___128
                                                                    =
                                                                    let uu___129
                                                                    =
                                                                    let uu___130
                                                                    =
                                                                    text
                                                                    "Place output in directory  dir" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "odir",
                                                                    (PostProcessed
                                                                    (pp_validate_dir,
                                                                    (PathStr
                                                                    "dir"))),
                                                                    uu___130) in
                                                                    let uu___130
                                                                    =
                                                                    let uu___131
                                                                    =
                                                                    let uu___132
                                                                    =
                                                                    text
                                                                    "Output the result of --dep into this file instead of to standard output." in
                                                                    (FStarC_Getopt.noshort,
                                                                    "output_deps_to",
                                                                    (PathStr
                                                                    "file"),
                                                                    uu___132) in
                                                                    let uu___132
                                                                    =
                                                                    let uu___133
                                                                    =
                                                                    let uu___134
                                                                    =
                                                                    text
                                                                    "Use a custom Prims.fst file. Do not use if you do not know exactly what you're doing." in
                                                                    (FStarC_Getopt.noshort,
                                                                    "prims",
                                                                    (PathStr
                                                                    "file"),
                                                                    uu___134) in
                                                                    let uu___134
                                                                    =
                                                                    let uu___135
                                                                    =
                                                                    let uu___136
                                                                    =
                                                                    text
                                                                    "Print the types of bound variables" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "print_bound_var_types",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    uu___136) in
                                                                    let uu___136
                                                                    =
                                                                    let uu___137
                                                                    =
                                                                    let uu___138
                                                                    =
                                                                    text
                                                                    "Print inferred predicate transformers for all computation types" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "print_effect_args",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    uu___138) in
                                                                    let uu___138
                                                                    =
                                                                    let uu___139
                                                                    =
                                                                    let uu___140
                                                                    =
                                                                    text
                                                                    "Print the errors generated by declarations marked with expect_failure, useful for debugging error locations" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "print_expected_failures",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    uu___140) in
                                                                    let uu___140
                                                                    =
                                                                    let uu___141
                                                                    =
                                                                    let uu___142
                                                                    =
                                                                    text
                                                                    "Print full names of variables" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "print_full_names",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    uu___142) in
                                                                    let uu___142
                                                                    =
                                                                    let uu___143
                                                                    =
                                                                    let uu___144
                                                                    =
                                                                    text
                                                                    "Print implicit arguments" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "print_implicits",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    uu___144) in
                                                                    let uu___144
                                                                    =
                                                                    let uu___145
                                                                    =
                                                                    let uu___146
                                                                    =
                                                                    text
                                                                    "Print universes" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "print_universes",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    uu___146) in
                                                                    let uu___146
                                                                    =
                                                                    let uu___147
                                                                    =
                                                                    let uu___148
                                                                    =
                                                                    text
                                                                    "Print Z3 statistics for each SMT query (details such as relevant modules, facts, etc. for each proof)" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "print_z3_statistics",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    uu___148) in
                                                                    let uu___148
                                                                    =
                                                                    let uu___149
                                                                    =
                                                                    let uu___150
                                                                    =
                                                                    text
                                                                    "Print full names (deprecated; use --print_full_names instead)" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "prn",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    uu___150) in
                                                                    let uu___150
                                                                    =
                                                                    let uu___151
                                                                    =
                                                                    let uu___152
                                                                    =
                                                                    text
                                                                    "Proof recovery mode: before failing an SMT query, retry 3 times, increasing rlimits. If the query goes through after retrying, verification will succeed, but a warning will be emitted. This feature is useful to restore a project after some change to its libraries or F* upgrade. Importantly, then, this option cannot be used in a pragma (#set-options, etc)." in
                                                                    (FStarC_Getopt.noshort,
                                                                    "proof_recovery",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    uu___152) in
                                                                    let uu___152
                                                                    =
                                                                    let uu___153
                                                                    =
                                                                    let uu___154
                                                                    =
                                                                    let uu___155
                                                                    =
                                                                    text
                                                                    "Repeats SMT queries to check for robustness" in
                                                                    let uu___156
                                                                    =
                                                                    let uu___157
                                                                    =
                                                                    let uu___158
                                                                    =
                                                                    let uu___159
                                                                    =
                                                                    text
                                                                    "--quake N/M repeats each query checks that it succeeds at least N out of M times, aborting early if possible" in
                                                                    let uu___160
                                                                    =
                                                                    let uu___161
                                                                    =
                                                                    text
                                                                    "--quake N/M/k works as above, except it will unconditionally run M times" in
                                                                    let uu___162
                                                                    =
                                                                    let uu___163
                                                                    =
                                                                    text
                                                                    "--quake N is an alias for --quake N/N" in
                                                                    let uu___164
                                                                    =
                                                                    let uu___165
                                                                    =
                                                                    text
                                                                    "--quake N/k is an alias for --quake N/N/k" in
                                                                    [uu___165] in
                                                                    uu___163
                                                                    ::
                                                                    uu___164 in
                                                                    uu___161
                                                                    ::
                                                                    uu___162 in
                                                                    uu___159
                                                                    ::
                                                                    uu___160 in
                                                                    FStarC_Errors_Msg.bulleted
                                                                    uu___158 in
                                                                    let uu___158
                                                                    =
                                                                    text
                                                                    "Using --quake disables --retry. When quake testing, queries are not splitted for error reporting unless '--split_queries always' is given. Queries from the smt_sync tactic are not quake-tested." in
                                                                    FStarC_Pprint.op_Hat_Hat
                                                                    uu___157
                                                                    uu___158 in
                                                                    FStarC_Pprint.op_Hat_Hat
                                                                    uu___155
                                                                    uu___156 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "quake",
                                                                    (PostProcessed
                                                                    ((fun
                                                                    uu___155
                                                                    ->
                                                                    match uu___155
                                                                    with
                                                                    | 
                                                                    String s
                                                                    ->
                                                                    let uu___156
                                                                    =
                                                                    interp_quake_arg
                                                                    s in
                                                                    (match uu___156
                                                                    with
                                                                    | 
                                                                    (min,
                                                                    max, k)
                                                                    ->
                                                                    (set_option
                                                                    "quake_lo"
                                                                    (Int min);
                                                                    set_option
                                                                    "quake_hi"
                                                                    (Int max);
                                                                    set_option
                                                                    "quake_keep"
                                                                    (Bool k);
                                                                    set_option
                                                                    "retry"
                                                                    (Bool
                                                                    false);
                                                                    String s))
                                                                    | 
                                                                    uu___156
                                                                    ->
                                                                    failwith
                                                                    "impos"),
                                                                    (SimpleStr
                                                                    "positive integer or pair of positive integers"))),
                                                                    uu___154) in
                                                                    let uu___154
                                                                    =
                                                                    let uu___155
                                                                    =
                                                                    let uu___156
                                                                    =
                                                                    text
                                                                    "Keep a running cache of SMT queries to make verification faster. Only available in the interactive mode. NOTE: This feature is experimental and potentially unsound! Hence why\n          it is not allowed in batch mode (where it is also less useful). If you\n          find a query that is mistakenly accepted with the cache, please\n          report a bug to the F* issue tracker on GitHub." in
                                                                    (FStarC_Getopt.noshort,
                                                                    "query_cache",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    uu___156) in
                                                                    let uu___156
                                                                    =
                                                                    let uu___157
                                                                    =
                                                                    let uu___158
                                                                    =
                                                                    text
                                                                    "Print SMT query statistics" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "query_stats",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    uu___158) in
                                                                    let uu___158
                                                                    =
                                                                    let uu___159
                                                                    =
                                                                    let uu___160
                                                                    =
                                                                    text
                                                                    "Read a checked file and dump it to standard output." in
                                                                    (FStarC_Getopt.noshort,
                                                                    "read_checked_file",
                                                                    (PathStr
                                                                    "path"),
                                                                    uu___160) in
                                                                    let uu___160
                                                                    =
                                                                    let uu___161
                                                                    =
                                                                    let uu___162
                                                                    =
                                                                    text
                                                                    "Read a Karamel binary file and dump it to standard output." in
                                                                    (FStarC_Getopt.noshort,
                                                                    "read_krml_file",
                                                                    (PathStr
                                                                    "path"),
                                                                    uu___162) in
                                                                    let uu___162
                                                                    =
                                                                    let uu___163
                                                                    =
                                                                    let uu___164
                                                                    =
                                                                    text
                                                                    "Record a database of hints for efficient proof replay" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "record_hints",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    uu___164) in
                                                                    let uu___164
                                                                    =
                                                                    let uu___165
                                                                    =
                                                                    let uu___166
                                                                    =
                                                                    text
                                                                    "Record the state of options used to check each sigelt, useful for the `check_with` attribute and metaprogramming. Note that this implies a performance hit and increases the size of checked files." in
                                                                    (FStarC_Getopt.noshort,
                                                                    "record_options",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    uu___166) in
                                                                    let uu___166
                                                                    =
                                                                    let uu___167
                                                                    =
                                                                    let uu___168
                                                                    =
                                                                    text
                                                                    "Retry each SMT query N times and succeed on the first try. Using --retry disables --quake." in
                                                                    (FStarC_Getopt.noshort,
                                                                    "retry",
                                                                    (PostProcessed
                                                                    ((fun
                                                                    uu___169
                                                                    ->
                                                                    match uu___169
                                                                    with
                                                                    | 
                                                                    Int i ->
                                                                    (set_option
                                                                    "quake_lo"
                                                                    (Int
                                                                    Prims.int_one);
                                                                    set_option
                                                                    "quake_hi"
                                                                    (Int i);
                                                                    set_option
                                                                    "quake_keep"
                                                                    (Bool
                                                                    false);
                                                                    set_option
                                                                    "retry"
                                                                    (Bool
                                                                    true);
                                                                    Bool true)
                                                                    | 
                                                                    uu___170
                                                                    ->
                                                                    failwith
                                                                    "impos"),
                                                                    (IntStr
                                                                    "positive integer"))),
                                                                    uu___168) in
                                                                    let uu___168
                                                                    =
                                                                    let uu___169
                                                                    =
                                                                    let uu___170
                                                                    =
                                                                    text
                                                                    "Optimistically, attempt using the recorded hint for  toplevel_name (a top-level name in the current module) when trying to verify some other term 'g'" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "reuse_hint_for",
                                                                    (SimpleStr
                                                                    "toplevel_name"),
                                                                    uu___170) in
                                                                    let uu___170
                                                                    =
                                                                    let uu___171
                                                                    =
                                                                    let uu___172
                                                                    =
                                                                    text
                                                                    "Report every use of an escape hatch, include assume, admit, etc." in
                                                                    (FStarC_Getopt.noshort,
                                                                    "report_assumes",
                                                                    (EnumStr
                                                                    ["warn";
                                                                    "error"]),
                                                                    uu___172) in
                                                                    let uu___172
                                                                    =
                                                                    let uu___173
                                                                    =
                                                                    let uu___174
                                                                    =
                                                                    text
                                                                    "Disable all non-critical output" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "silent",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    uu___174) in
                                                                    let uu___174
                                                                    =
                                                                    let uu___175
                                                                    =
                                                                    let uu___176
                                                                    =
                                                                    text
                                                                    "Path to the Z3 SMT solver (we could eventually support other solvers)" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "smt",
                                                                    (PathStr
                                                                    "path"),
                                                                    uu___176) in
                                                                    let uu___176
                                                                    =
                                                                    let uu___177
                                                                    =
                                                                    let uu___178
                                                                    =
                                                                    text
                                                                    "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "smtencoding.elim_box",
                                                                    BoolStr,
                                                                    uu___178) in
                                                                    let uu___178
                                                                    =
                                                                    let uu___179
                                                                    =
                                                                    let uu___180
                                                                    =
                                                                    let uu___181
                                                                    =
                                                                    text
                                                                    "Control the representation of non-linear arithmetic functions in the SMT encoding:" in
                                                                    let uu___182
                                                                    =
                                                                    let uu___183
                                                                    =
                                                                    let uu___184
                                                                    =
                                                                    let uu___185
                                                                    =
                                                                    text
                                                                    "if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'" in
                                                                    let uu___186
                                                                    =
                                                                    let uu___187
                                                                    =
                                                                    text
                                                                    "if 'native' use '*, div, mod'" in
                                                                    let uu___188
                                                                    =
                                                                    let uu___189
                                                                    =
                                                                    text
                                                                    "if 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'" in
                                                                    [uu___189] in
                                                                    uu___187
                                                                    ::
                                                                    uu___188 in
                                                                    uu___185
                                                                    ::
                                                                    uu___186 in
                                                                    FStarC_Errors_Msg.bulleted
                                                                    uu___184 in
                                                                    let uu___184
                                                                    =
                                                                    text
                                                                    "(default 'boxwrap')" in
                                                                    FStarC_Pprint.op_Hat_Hat
                                                                    uu___183
                                                                    uu___184 in
                                                                    FStarC_Pprint.op_Hat_Hat
                                                                    uu___181
                                                                    uu___182 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "smtencoding.nl_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "wrapped";
                                                                    "boxwrap"]),
                                                                    uu___180) in
                                                                    let uu___180
                                                                    =
                                                                    let uu___181
                                                                    =
                                                                    let uu___182
                                                                    =
                                                                    let uu___183
                                                                    =
                                                                    text
                                                                    "Toggle the representation of linear arithmetic functions in the SMT encoding:" in
                                                                    let uu___184
                                                                    =
                                                                    let uu___185
                                                                    =
                                                                    let uu___186
                                                                    =
                                                                    let uu___187
                                                                    =
                                                                    text
                                                                    "if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'" in
                                                                    let uu___188
                                                                    =
                                                                    let uu___189
                                                                    =
                                                                    text
                                                                    "if 'native', use '+, -, -'" in
                                                                    [uu___189] in
                                                                    uu___187
                                                                    ::
                                                                    uu___188 in
                                                                    FStarC_Errors_Msg.bulleted
                                                                    uu___186 in
                                                                    let uu___186
                                                                    =
                                                                    text
                                                                    "(default 'boxwrap')" in
                                                                    FStarC_Pprint.op_Hat_Hat
                                                                    uu___185
                                                                    uu___186 in
                                                                    FStarC_Pprint.op_Hat_Hat
                                                                    uu___183
                                                                    uu___184 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "smtencoding.l_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "boxwrap"]),
                                                                    uu___182) in
                                                                    let uu___182
                                                                    =
                                                                    let uu___183
                                                                    =
                                                                    let uu___184
                                                                    =
                                                                    text
                                                                    "Include an axiom in the SMT encoding to introduce proof-irrelevance from a constructive proof" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "smtencoding.valid_intro",
                                                                    BoolStr,
                                                                    uu___184) in
                                                                    let uu___184
                                                                    =
                                                                    let uu___185
                                                                    =
                                                                    let uu___186
                                                                    =
                                                                    text
                                                                    "Include an axiom in the SMT encoding to eliminate proof-irrelevance into the existence of a proof witness" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "smtencoding.valid_elim",
                                                                    BoolStr,
                                                                    uu___186) in
                                                                    let uu___186
                                                                    =
                                                                    let uu___187
                                                                    =
                                                                    let uu___188
                                                                    =
                                                                    let uu___189
                                                                    =
                                                                    text
                                                                    "Split SMT verification conditions into several separate queries, one per goal. Helps with localizing errors." in
                                                                    let uu___190
                                                                    =
                                                                    let uu___191
                                                                    =
                                                                    let uu___192
                                                                    =
                                                                    text
                                                                    "Use 'no' to disable (this may reduce the quality of error messages)." in
                                                                    let uu___193
                                                                    =
                                                                    let uu___194
                                                                    =
                                                                    text
                                                                    "Use 'on_failure' to split queries and retry when discharging fails (the default)" in
                                                                    let uu___195
                                                                    =
                                                                    let uu___196
                                                                    =
                                                                    text
                                                                    "Use 'yes' to always split." in
                                                                    [uu___196] in
                                                                    uu___194
                                                                    ::
                                                                    uu___195 in
                                                                    uu___192
                                                                    ::
                                                                    uu___193 in
                                                                    FStarC_Errors_Msg.bulleted
                                                                    uu___191 in
                                                                    FStarC_Pprint.op_Hat_Hat
                                                                    uu___189
                                                                    uu___190 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "split_queries",
                                                                    (EnumStr
                                                                    ["no";
                                                                    "on_failure";
                                                                    "always"]),
                                                                    uu___188) in
                                                                    let uu___188
                                                                    =
                                                                    let uu___189
                                                                    =
                                                                    let uu___190
                                                                    =
                                                                    text
                                                                    "Do not use the lexical scope of tactics to improve binder names" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "tactic_raw_binders",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    uu___190) in
                                                                    let uu___190
                                                                    =
                                                                    let uu___191
                                                                    =
                                                                    let uu___192
                                                                    =
                                                                    text
                                                                    "Do not recover from metaprogramming errors, and abort if one occurs" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "tactics_failhard",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    uu___192) in
                                                                    let uu___192
                                                                    =
                                                                    let uu___193
                                                                    =
                                                                    let uu___194
                                                                    =
                                                                    text
                                                                    "Print some rough information on tactics, such as the time they take to run" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "tactics_info",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    uu___194) in
                                                                    let uu___194
                                                                    =
                                                                    let uu___195
                                                                    =
                                                                    let uu___196
                                                                    =
                                                                    text
                                                                    "Print a depth-indexed trace of tactic execution (Warning: very verbose)" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "tactic_trace",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    uu___196) in
                                                                    let uu___196
                                                                    =
                                                                    let uu___197
                                                                    =
                                                                    let uu___198
                                                                    =
                                                                    text
                                                                    "Trace tactics up to a certain binding depth" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "tactic_trace_d",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    uu___198) in
                                                                    let uu___198
                                                                    =
                                                                    let uu___199
                                                                    =
                                                                    let uu___200
                                                                    =
                                                                    text
                                                                    "Use NBE to evaluate metaprograms (experimental)" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "__tactics_nbe",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    uu___200) in
                                                                    let uu___200
                                                                    =
                                                                    let uu___201
                                                                    =
                                                                    let uu___202
                                                                    =
                                                                    text
                                                                    "Attempt to normalize definitions marked as tcnorm (default 'true')" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "tcnorm",
                                                                    BoolStr,
                                                                    uu___202) in
                                                                    let uu___202
                                                                    =
                                                                    let uu___203
                                                                    =
                                                                    let uu___204
                                                                    =
                                                                    text
                                                                    "Print the time it takes to verify each top-level definition. This is just an alias for an invocation of the profiler, so it may not work well if combined with --profile. In particular, it implies --profile_group_by_decl." in
                                                                    (FStarC_Getopt.noshort,
                                                                    "timing",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    uu___204) in
                                                                    let uu___204
                                                                    =
                                                                    let uu___205
                                                                    =
                                                                    let uu___206
                                                                    =
                                                                    text
                                                                    "Attach stack traces on errors" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "trace_error",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    uu___206) in
                                                                    let uu___206
                                                                    =
                                                                    let uu___207
                                                                    =
                                                                    let uu___208
                                                                    =
                                                                    text
                                                                    "Emit output formatted for debugging" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "ugly",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    uu___208) in
                                                                    let uu___208
                                                                    =
                                                                    let uu___209
                                                                    =
                                                                    let uu___210
                                                                    =
                                                                    text
                                                                    "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "unthrottle_inductives",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    uu___210) in
                                                                    let uu___210
                                                                    =
                                                                    let uu___211
                                                                    =
                                                                    let uu___212
                                                                    =
                                                                    text
                                                                    "Allow tactics to run external processes. WARNING: checking an untrusted F* file while using this option can have disastrous effects." in
                                                                    (FStarC_Getopt.noshort,
                                                                    "unsafe_tactic_exec",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    uu___212) in
                                                                    let uu___212
                                                                    =
                                                                    let uu___213
                                                                    =
                                                                    let uu___214
                                                                    =
                                                                    text
                                                                    "Use equality constraints when comparing higher-order types (Temporary)" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "use_eq_at_higher_order",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    uu___214) in
                                                                    let uu___214
                                                                    =
                                                                    let uu___215
                                                                    =
                                                                    let uu___216
                                                                    =
                                                                    text
                                                                    "Use a previously recorded hints database for proof replay" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "use_hints",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    uu___216) in
                                                                    let uu___216
                                                                    =
                                                                    let uu___217
                                                                    =
                                                                    let uu___218
                                                                    =
                                                                    text
                                                                    "Admit queries if their hash matches the hash recorded in the hints database" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "use_hint_hashes",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    uu___218) in
                                                                    let uu___218
                                                                    =
                                                                    let uu___219
                                                                    =
                                                                    let uu___220
                                                                    =
                                                                    text
                                                                    "Use compiled tactics from  path" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "use_native_tactics",
                                                                    (PathStr
                                                                    "path"),
                                                                    uu___220) in
                                                                    let uu___220
                                                                    =
                                                                    let uu___221
                                                                    =
                                                                    let uu___222
                                                                    =
                                                                    text
                                                                    "Do not run plugins natively and interpret them as usual instead" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "no_plugins",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    uu___222) in
                                                                    let uu___222
                                                                    =
                                                                    let uu___223
                                                                    =
                                                                    let uu___224
                                                                    =
                                                                    text
                                                                    "Do not run the tactic engine before discharging a VC" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "no_tactics",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    uu___224) in
                                                                    let uu___224
                                                                    =
                                                                    let uu___225
                                                                    =
                                                                    let uu___226
                                                                    =
                                                                    text
                                                                    "Prunes the context to include only the facts from the given namespace or fact id. Facts can be include or excluded using the [+|-] qualifier. For example --using_facts_from '* -FStarC.Reflection +FStarC.Compiler.List -FStarC.Compiler.List.Tot' will remove all facts from FStarC.Compiler.List.Tot.*, retain all remaining facts from FStarC.Compiler.List.*, remove all facts from FStarC.Reflection.*, and retain all the rest. Note, the '+' is optional: --using_facts_from 'FStarC.Compiler.List' is equivalent to --using_facts_from '+FStarC.Compiler.List'. Multiple uses of this option accumulate, e.g., --using_facts_from A --using_facts_from B is interpreted as --using_facts_from A^B." in
                                                                    (FStarC_Getopt.noshort,
                                                                    "using_facts_from",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | fact id)'")),
                                                                    uu___226) in
                                                                    let uu___226
                                                                    =
                                                                    let uu___227
                                                                    =
                                                                    let uu___228
                                                                    =
                                                                    text
                                                                    "This does nothing and will be removed" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "__temp_fast_implicits",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    uu___228) in
                                                                    let uu___228
                                                                    =
                                                                    let uu___229
                                                                    =
                                                                    let uu___230
                                                                    =
                                                                    text
                                                                    "Display version number" in
                                                                    (118,
                                                                    "version",
                                                                    (WithSideEffect
                                                                    ((fun
                                                                    uu___231
                                                                    ->
                                                                    display_version
                                                                    ();
                                                                    FStarC_Compiler_Effect.exit
                                                                    Prims.int_zero),
                                                                    (Const
                                                                    (Bool
                                                                    true)))),
                                                                    uu___230) in
                                                                    let uu___230
                                                                    =
                                                                    let uu___231
                                                                    =
                                                                    let uu___232
                                                                    =
                                                                    text
                                                                    "Warn when (a -> b) is desugared to (a -> Tot b)" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "warn_default_effects",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    uu___232) in
                                                                    let uu___232
                                                                    =
                                                                    let uu___233
                                                                    =
                                                                    let uu___234
                                                                    =
                                                                    text
                                                                    "Z3 command line options" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "z3cliopt",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "option")),
                                                                    uu___234) in
                                                                    let uu___234
                                                                    =
                                                                    let uu___235
                                                                    =
                                                                    let uu___236
                                                                    =
                                                                    text
                                                                    "Z3 options in smt2 format" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "z3smtopt",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "option")),
                                                                    uu___236) in
                                                                    let uu___236
                                                                    =
                                                                    let uu___237
                                                                    =
                                                                    let uu___238
                                                                    =
                                                                    text
                                                                    "Restart Z3 after each query; useful for ensuring proof robustness" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "z3refresh",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    uu___238) in
                                                                    let uu___238
                                                                    =
                                                                    let uu___239
                                                                    =
                                                                    let uu___240
                                                                    =
                                                                    text
                                                                    "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "z3rlimit",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    uu___240) in
                                                                    let uu___240
                                                                    =
                                                                    let uu___241
                                                                    =
                                                                    let uu___242
                                                                    =
                                                                    text
                                                                    "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "z3rlimit_factor",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    uu___242) in
                                                                    let uu___242
                                                                    =
                                                                    let uu___243
                                                                    =
                                                                    let uu___244
                                                                    =
                                                                    text
                                                                    "Set the Z3 random seed (default 0)" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "z3seed",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    uu___244) in
                                                                    let uu___244
                                                                    =
                                                                    let uu___245
                                                                    =
                                                                    let uu___246
                                                                    =
                                                                    text
                                                                    "Set the version of Z3 that is to be used. Default: 4.8.5" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "z3version",
                                                                    (SimpleStr
                                                                    "version"),
                                                                    uu___246) in
                                                                    let uu___246
                                                                    =
                                                                    let uu___247
                                                                    =
                                                                    let uu___248
                                                                    =
                                                                    text
                                                                    "Don't check positivity of inductive types" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "__no_positivity",
                                                                    (WithSideEffect
                                                                    ((fun
                                                                    uu___249
                                                                    ->
                                                                    if
                                                                    warn_unsafe
                                                                    then
                                                                    option_warning_callback
                                                                    "__no_positivity"
                                                                    else ()),
                                                                    (Const
                                                                    (Bool
                                                                    true)))),
                                                                    uu___248) in
                                                                    let uu___248
                                                                    =
                                                                    let uu___249
                                                                    =
                                                                    let uu___250
                                                                    =
                                                                    let uu___251
                                                                    =
                                                                    text
                                                                    "The [-warn_error] option follows the OCaml syntax, namely:" in
                                                                    let uu___252
                                                                    =
                                                                    let uu___253
                                                                    =
                                                                    let uu___254
                                                                    =
                                                                    text
                                                                    "[r] is a range of warnings (either a number [n], or a range [n..n])" in
                                                                    let uu___255
                                                                    =
                                                                    let uu___256
                                                                    =
                                                                    text
                                                                    "[-r] silences range [r]" in
                                                                    let uu___257
                                                                    =
                                                                    let uu___258
                                                                    =
                                                                    text
                                                                    "[+r] enables range [r] as warnings (NOTE: \"enabling\" an error will downgrade it to a warning)" in
                                                                    let uu___259
                                                                    =
                                                                    let uu___260
                                                                    =
                                                                    text
                                                                    "[@r] makes range [r] fatal." in
                                                                    [uu___260] in
                                                                    uu___258
                                                                    ::
                                                                    uu___259 in
                                                                    uu___256
                                                                    ::
                                                                    uu___257 in
                                                                    uu___254
                                                                    ::
                                                                    uu___255 in
                                                                    FStarC_Errors_Msg.bulleted
                                                                    uu___253 in
                                                                    FStarC_Pprint.op_Hat_Hat
                                                                    uu___251
                                                                    uu___252 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "warn_error",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "")),
                                                                    uu___250) in
                                                                    let uu___250
                                                                    =
                                                                    let uu___251
                                                                    =
                                                                    let uu___252
                                                                    =
                                                                    text
                                                                    "Use normalization by evaluation as the default normalization strategy (default 'false')" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "use_nbe",
                                                                    BoolStr,
                                                                    uu___252) in
                                                                    let uu___252
                                                                    =
                                                                    let uu___253
                                                                    =
                                                                    let uu___254
                                                                    =
                                                                    text
                                                                    "Use normalization by evaluation for normalizing terms before extraction (default 'false')" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "use_nbe_for_extraction",
                                                                    BoolStr,
                                                                    uu___254) in
                                                                    let uu___254
                                                                    =
                                                                    let uu___255
                                                                    =
                                                                    let uu___256
                                                                    =
                                                                    text
                                                                    "Enforce trivial preconditions for unannotated effectful functions (default 'true')" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "trivial_pre_for_unannotated_effectful_fns",
                                                                    BoolStr,
                                                                    uu___256) in
                                                                    let uu___256
                                                                    =
                                                                    let uu___257
                                                                    =
                                                                    let uu___258
                                                                    =
                                                                    text
                                                                    "Debug messages for embeddings/unembeddings of natively compiled terms" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "__debug_embedding",
                                                                    (WithSideEffect
                                                                    ((fun
                                                                    uu___259
                                                                    ->
                                                                    FStarC_Compiler_Effect.op_Colon_Equals
                                                                    debug_embedding
                                                                    true),
                                                                    (Const
                                                                    (Bool
                                                                    true)))),
                                                                    uu___258) in
                                                                    let uu___258
                                                                    =
                                                                    let uu___259
                                                                    =
                                                                    let uu___260
                                                                    =
                                                                    text
                                                                    "Eagerly embed and unembed terms to primitive operations and plugins: not recommended except for benchmarking" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "eager_embedding",
                                                                    (WithSideEffect
                                                                    ((fun
                                                                    uu___261
                                                                    ->
                                                                    FStarC_Compiler_Effect.op_Colon_Equals
                                                                    eager_embedding
                                                                    true),
                                                                    (Const
                                                                    (Bool
                                                                    true)))),
                                                                    uu___260) in
                                                                    let uu___260
                                                                    =
                                                                    let uu___261
                                                                    =
                                                                    let uu___262
                                                                    =
                                                                    text
                                                                    "Emit profiles grouped by declaration rather than by module" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "profile_group_by_decl",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    uu___262) in
                                                                    let uu___262
                                                                    =
                                                                    let uu___263
                                                                    =
                                                                    let uu___264
                                                                    =
                                                                    text
                                                                    "Specific source locations in the compiler are instrumented with profiling counters. Pass `--profile_component FStarC.TypeChecker` to enable all counters in the FStarC.TypeChecker namespace. This option is a module or namespace selector, like many other options (e.g., `--extract`)" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "profile_component",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | module | identifier)'")),
                                                                    uu___264) in
                                                                    let uu___264
                                                                    =
                                                                    let uu___265
                                                                    =
                                                                    let uu___266
                                                                    =
                                                                    text
                                                                    "Profiling can be enabled when the compiler is processing a given set of source modules. Pass `--profile FStar.Pervasives` to enable profiling when the compiler is processing any module in FStar.Pervasives. This option is a module or namespace selector, like many other options (e.g., `--extract`)" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "profile",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
                                                                    uu___266) in
                                                                    let uu___266
                                                                    =
                                                                    let uu___267
                                                                    =
                                                                    let uu___268
                                                                    =
                                                                    text
                                                                    "Display this information" in
                                                                    (104,
                                                                    "help",
                                                                    (WithSideEffect
                                                                    ((fun
                                                                    uu___269
                                                                    ->
                                                                    (
                                                                    let uu___271
                                                                    =
                                                                    specs
                                                                    warn_unsafe in
                                                                    display_usage_aux
                                                                    uu___271);
                                                                    FStarC_Compiler_Effect.exit
                                                                    Prims.int_zero),
                                                                    (Const
                                                                    (Bool
                                                                    true)))),
                                                                    uu___268) in
                                                                    let uu___268
                                                                    =
                                                                    let uu___269
                                                                    =
                                                                    let uu___270
                                                                    =
                                                                    text
                                                                    "List all debug keys and exit" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "list_debug_keys",
                                                                    (WithSideEffect
                                                                    ((fun
                                                                    uu___271
                                                                    ->
                                                                    display_debug_keys
                                                                    ();
                                                                    FStarC_Compiler_Effect.exit
                                                                    Prims.int_zero),
                                                                    (Const
                                                                    (Bool
                                                                    true)))),
                                                                    uu___270) in
                                                                    let uu___270
                                                                    =
                                                                    let uu___271
                                                                    =
                                                                    let uu___272
                                                                    =
                                                                    text
                                                                    "List all registered plugins and exit" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "list_plugins",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    uu___272) in
                                                                    let uu___272
                                                                    =
                                                                    let uu___273
                                                                    =
                                                                    let uu___274
                                                                    =
                                                                    text
                                                                    "Print the root of the F* installation and exit" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "locate",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    uu___274) in
                                                                    let uu___274
                                                                    =
                                                                    let uu___275
                                                                    =
                                                                    let uu___276
                                                                    =
                                                                    text
                                                                    "Print the root of the F* library and exit" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "locate_lib",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    uu___276) in
                                                                    let uu___276
                                                                    =
                                                                    let uu___277
                                                                    =
                                                                    let uu___278
                                                                    =
                                                                    text
                                                                    "Print the root of the built OCaml F* library and exit" in
                                                                    (FStarC_Getopt.noshort,
                                                                    "locate_ocaml",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    uu___278) in
                                                                    let uu___278
                                                                    =
                                                                    let uu___279
                                                                    =
                                                                    let uu___280
                                                                    =
                                                                    text
                                                                    "With no arguments: print shell code to set up an environment with the OCaml libraries in scope (similar to 'opam env'). With arguments: run a command in that environment. NOTE: this must be the FIRST argument passed to F* and other options are NOT processed." in
                                                                    (FStarC_Getopt.noshort,
                                                                    "ocamlenv",
                                                                    (WithSideEffect
                                                                    ((fun
                                                                    uu___281
                                                                    ->
                                                                    FStarC_Compiler_Util.print_error
                                                                    "--ocamlenv must be the first argument, see fstar.exe --help for details\n";
                                                                    FStarC_Compiler_Effect.exit
                                                                    Prims.int_one),
                                                                    (Const
                                                                    (Bool
                                                                    true)))),
                                                                    uu___280) in
                                                                    [uu___279] in
                                                                    uu___277
                                                                    ::
                                                                    uu___278 in
                                                                    uu___275
                                                                    ::
                                                                    uu___276 in
                                                                    uu___273
                                                                    ::
                                                                    uu___274 in
                                                                    uu___271
                                                                    ::
                                                                    uu___272 in
                                                                    uu___269
                                                                    ::
                                                                    uu___270 in
                                                                    uu___267
                                                                    ::
                                                                    uu___268 in
                                                                    uu___265
                                                                    ::
                                                                    uu___266 in
                                                                    uu___263
                                                                    ::
                                                                    uu___264 in
                                                                    uu___261
                                                                    ::
                                                                    uu___262 in
                                                                    uu___259
                                                                    ::
                                                                    uu___260 in
                                                                    uu___257
                                                                    ::
                                                                    uu___258 in
                                                                    uu___255
                                                                    ::
                                                                    uu___256 in
                                                                    uu___253
                                                                    ::
                                                                    uu___254 in
                                                                    uu___251
                                                                    ::
                                                                    uu___252 in
                                                                    uu___249
                                                                    ::
                                                                    uu___250 in
                                                                    uu___247
                                                                    ::
                                                                    uu___248 in
                                                                    uu___245
                                                                    ::
                                                                    uu___246 in
                                                                    uu___243
                                                                    ::
                                                                    uu___244 in
                                                                    uu___241
                                                                    ::
                                                                    uu___242 in
                                                                    uu___239
                                                                    ::
                                                                    uu___240 in
                                                                    uu___237
                                                                    ::
                                                                    uu___238 in
                                                                    uu___235
                                                                    ::
                                                                    uu___236 in
                                                                    uu___233
                                                                    ::
                                                                    uu___234 in
                                                                    uu___231
                                                                    ::
                                                                    uu___232 in
                                                                    uu___229
                                                                    ::
                                                                    uu___230 in
                                                                    uu___227
                                                                    ::
                                                                    uu___228 in
                                                                    uu___225
                                                                    ::
                                                                    uu___226 in
                                                                    uu___223
                                                                    ::
                                                                    uu___224 in
                                                                    uu___221
                                                                    ::
                                                                    uu___222 in
                                                                    uu___219
                                                                    ::
                                                                    uu___220 in
                                                                    uu___217
                                                                    ::
                                                                    uu___218 in
                                                                    uu___215
                                                                    ::
                                                                    uu___216 in
                                                                    uu___213
                                                                    ::
                                                                    uu___214 in
                                                                    uu___211
                                                                    ::
                                                                    uu___212 in
                                                                    uu___209
                                                                    ::
                                                                    uu___210 in
                                                                    uu___207
                                                                    ::
                                                                    uu___208 in
                                                                    uu___205
                                                                    ::
                                                                    uu___206 in
                                                                    uu___203
                                                                    ::
                                                                    uu___204 in
                                                                    uu___201
                                                                    ::
                                                                    uu___202 in
                                                                    uu___199
                                                                    ::
                                                                    uu___200 in
                                                                    uu___197
                                                                    ::
                                                                    uu___198 in
                                                                    uu___195
                                                                    ::
                                                                    uu___196 in
                                                                    uu___193
                                                                    ::
                                                                    uu___194 in
                                                                    uu___191
                                                                    ::
                                                                    uu___192 in
                                                                    uu___189
                                                                    ::
                                                                    uu___190 in
                                                                    uu___187
                                                                    ::
                                                                    uu___188 in
                                                                    uu___185
                                                                    ::
                                                                    uu___186 in
                                                                    uu___183
                                                                    ::
                                                                    uu___184 in
                                                                    uu___181
                                                                    ::
                                                                    uu___182 in
                                                                    uu___179
                                                                    ::
                                                                    uu___180 in
                                                                    uu___177
                                                                    ::
                                                                    uu___178 in
                                                                    uu___175
                                                                    ::
                                                                    uu___176 in
                                                                    uu___173
                                                                    ::
                                                                    uu___174 in
                                                                    uu___171
                                                                    ::
                                                                    uu___172 in
                                                                    uu___169
                                                                    ::
                                                                    uu___170 in
                                                                    uu___167
                                                                    ::
                                                                    uu___168 in
                                                                    uu___165
                                                                    ::
                                                                    uu___166 in
                                                                    uu___163
                                                                    ::
                                                                    uu___164 in
                                                                    uu___161
                                                                    ::
                                                                    uu___162 in
                                                                    uu___159
                                                                    ::
                                                                    uu___160 in
                                                                    uu___157
                                                                    ::
                                                                    uu___158 in
                                                                    uu___155
                                                                    ::
                                                                    uu___156 in
                                                                    uu___153
                                                                    ::
                                                                    uu___154 in
                                                                    uu___151
                                                                    ::
                                                                    uu___152 in
                                                                    uu___149
                                                                    ::
                                                                    uu___150 in
                                                                    uu___147
                                                                    ::
                                                                    uu___148 in
                                                                    uu___145
                                                                    ::
                                                                    uu___146 in
                                                                    uu___143
                                                                    ::
                                                                    uu___144 in
                                                                    uu___141
                                                                    ::
                                                                    uu___142 in
                                                                    uu___139
                                                                    ::
                                                                    uu___140 in
                                                                    uu___137
                                                                    ::
                                                                    uu___138 in
                                                                    uu___135
                                                                    ::
                                                                    uu___136 in
                                                                    uu___133
                                                                    ::
                                                                    uu___134 in
                                                                    uu___131
                                                                    ::
                                                                    uu___132 in
                                                                    uu___129
                                                                    ::
                                                                    uu___130 in
                                                                    uu___127
                                                                    ::
                                                                    uu___128 in
                                                                    uu___125
                                                                    ::
                                                                    uu___126 in
                                                                    uu___123
                                                                    ::
                                                                    uu___124 in
                                                                    uu___121
                                                                    ::
                                                                    uu___122 in
                                                                    uu___119
                                                                    ::
                                                                    uu___120 in
                                                                    uu___117
                                                                    ::
                                                                    uu___118 in
                                                                    uu___115
                                                                    ::
                                                                    uu___116 in
                                                                    uu___113
                                                                    ::
                                                                    uu___114 in
                                                                    uu___111
                                                                    ::
                                                                    uu___112 in
                                                                    uu___109
                                                                    ::
                                                                    uu___110 in
                                                                    uu___107
                                                                    ::
                                                                    uu___108 in
                                                                    uu___105
                                                                    ::
                                                                    uu___106 in
                                                                    uu___103
                                                                    ::
                                                                    uu___104 in
                                                                    uu___101
                                                                    ::
                                                                    uu___102 in
                                                                    uu___99
                                                                    ::
                                                                    uu___100 in
                                                                    uu___97
                                                                    ::
                                                                    uu___98 in
                                                                    uu___95
                                                                    ::
                                                                    uu___96 in
                                                                    uu___93
                                                                    ::
                                                                    uu___94 in
                                                                    uu___91
                                                                    ::
                                                                    uu___92 in
                                                                    uu___89
                                                                    ::
                                                                    uu___90 in
                                                                    uu___87
                                                                    ::
                                                                    uu___88 in
                                                                    uu___85
                                                                    ::
                                                                    uu___86 in
                                                                    uu___83
                                                                    ::
                                                                    uu___84 in
                                                                    uu___81
                                                                    ::
                                                                    uu___82 in
                                                                    uu___79
                                                                    ::
                                                                    uu___80 in
                                                                    uu___77
                                                                    ::
                                                                    uu___78 in
                                                                    uu___75
                                                                    ::
                                                                    uu___76 in
                                                                    uu___73
                                                                    ::
                                                                    uu___74 in
                                                                    uu___71
                                                                    ::
                                                                    uu___72 in
                                                                    uu___69
                                                                    ::
                                                                    uu___70 in
                                                                    uu___67
                                                                    ::
                                                                    uu___68 in
                                                                    uu___65
                                                                    ::
                                                                    uu___66 in
                                                                  uu___63 ::
                                                                    uu___64 in
                                                                uu___61 ::
                                                                  uu___62 in
                                                              uu___59 ::
                                                                uu___60 in
                                                            uu___57 ::
                                                              uu___58 in
                                                          uu___55 :: uu___56 in
                                                        uu___53 :: uu___54 in
                                                      uu___51 :: uu___52 in
                                                    uu___49 :: uu___50 in
                                                  uu___47 :: uu___48 in
                                                uu___45 :: uu___46 in
                                              uu___43 :: uu___44 in
                                            uu___41 :: uu___42 in
                                          uu___39 :: uu___40 in
                                        uu___37 :: uu___38 in
                                      uu___35 :: uu___36 in
                                    uu___33 :: uu___34 in
                                  uu___31 :: uu___32 in
                                uu___29 :: uu___30 in
                              uu___27 :: uu___28 in
                            uu___25 :: uu___26 in
                          uu___23 :: uu___24 in
                        uu___21 :: uu___22 in
                      uu___19 :: uu___20 in
                    uu___17 :: uu___18 in
                  uu___15 :: uu___16 in
                uu___13 :: uu___14 in
              uu___11 :: uu___12 in
            uu___9 :: uu___10 in
          uu___7 :: uu___8 in
        uu___5 :: uu___6 in
      uu___3 :: uu___4 in
    uu___ :: uu___2
and (specs :
  Prims.bool -> (FStarC_Getopt.opt * FStarC_Pprint.document) Prims.list) =
  fun warn_unsafe ->
    let uu___ = specs_with_types warn_unsafe in
    FStarC_Compiler_List.map
      (fun uu___2 ->
         match uu___2 with
         | (short, long, typ, doc) ->
             let uu___3 =
               let uu___4 =
                 let uu___5 = arg_spec_of_opt_type long typ in
                 (short, long, uu___5) in
               mk_spec uu___4 in
             (uu___3, doc)) uu___
let (settable : Prims.string -> Prims.bool) =
  fun uu___ ->
    match uu___ with
    | "__temp_fast_implicits" -> true
    | "abort_on" -> true
    | "admit_except" -> true
    | "admit_smt_queries" -> true
    | "compat_pre_core" -> true
    | "compat_pre_typed_indexed_effects" -> true
    | "disallow_unification_guards" -> true
    | "debug" -> true
    | "debug_all" -> true
    | "debug_all_modules" -> true
    | "defensive" -> true
    | "detail_errors" -> true
    | "detail_hint_replay" -> true
    | "eager_subtyping" -> true
    | "error_contexts" -> true
    | "hide_uvar_nums" -> true
    | "hint_dir" -> true
    | "hint_file" -> true
    | "hint_info" -> true
    | "fuel" -> true
    | "ext" -> true
    | "ifuel" -> true
    | "initial_fuel" -> true
    | "initial_ifuel" -> true
    | "ide_id_info_off" -> true
    | "keep_query_captions" -> true
    | "load" -> true
    | "load_cmxs" -> true
    | "log_queries" -> true
    | "log_failing_queries" -> true
    | "log_types" -> true
    | "max_fuel" -> true
    | "max_ifuel" -> true
    | "no_plugins" -> true
    | "__no_positivity" -> true
    | "normalize_pure_terms_for_extraction" -> true
    | "no_smt" -> true
    | "no_tactics" -> true
    | "print_bound_var_types" -> true
    | "print_effect_args" -> true
    | "print_expected_failures" -> true
    | "print_full_names" -> true
    | "print_implicits" -> true
    | "print_universes" -> true
    | "print_z3_statistics" -> true
    | "prn" -> true
    | "quake_lo" -> true
    | "quake_hi" -> true
    | "quake_keep" -> true
    | "quake" -> true
    | "query_cache" -> true
    | "query_stats" -> true
    | "record_options" -> true
    | "retry" -> true
    | "reuse_hint_for" -> true
    | "report_assumes" -> true
    | "silent" -> true
    | "smtencoding.elim_box" -> true
    | "smtencoding.l_arith_repr" -> true
    | "smtencoding.nl_arith_repr" -> true
    | "smtencoding.valid_intro" -> true
    | "smtencoding.valid_elim" -> true
    | "split_queries" -> true
    | "tactic_raw_binders" -> true
    | "tactics_failhard" -> true
    | "tactics_info" -> true
    | "__tactics_nbe" -> true
    | "tactic_trace" -> true
    | "tactic_trace_d" -> true
    | "tcnorm" -> true
    | "timing" -> true
    | "trace_error" -> true
    | "ugly" -> true
    | "unthrottle_inductives" -> true
    | "use_eq_at_higher_order" -> true
    | "using_facts_from" -> true
    | "warn_error" -> true
    | "z3cliopt" -> true
    | "z3smtopt" -> true
    | "z3refresh" -> true
    | "z3rlimit" -> true
    | "z3rlimit_factor" -> true
    | "z3seed" -> true
    | "z3version" -> true
    | "trivial_pre_for_unannotated_effectful_fns" -> true
    | "profile_group_by_decl" -> true
    | "profile_component" -> true
    | "profile" -> true
    | uu___2 -> false
let (all_specs : (FStarC_Getopt.opt * FStarC_Pprint.document) Prims.list) =
  specs true
let (all_specs_getopt : FStarC_Getopt.opt Prims.list) =
  FStarC_Compiler_List.map FStar_Pervasives_Native.fst all_specs
let (all_specs_with_types :
  (FStarC_BaseTypes.char * Prims.string * opt_type * FStarC_Pprint.document)
    Prims.list)
  = specs_with_types true
let (settable_specs :
  ((FStarC_BaseTypes.char * Prims.string * unit FStarC_Getopt.opt_variant) *
    FStarC_Pprint.document) Prims.list)
  =
  FStarC_Compiler_List.filter
    (fun uu___ ->
       match uu___ with | ((uu___2, x, uu___3), uu___4) -> settable x)
    all_specs
let (uu___2 :
  (((unit -> FStarC_Getopt.parse_cmdline_res) -> unit) *
    (unit -> FStarC_Getopt.parse_cmdline_res)))
  =
  let callback = FStarC_Compiler_Util.mk_ref FStar_Pervasives_Native.None in
  let set1 f =
    FStarC_Compiler_Effect.op_Colon_Equals callback
      (FStar_Pervasives_Native.Some f) in
  let call uu___ =
    let uu___3 = FStarC_Compiler_Effect.op_Bang callback in
    match uu___3 with
    | FStar_Pervasives_Native.None ->
        failwith "Error flags callback not yet set"
    | FStar_Pervasives_Native.Some f -> f () in
  (set1, call)
let (set_error_flags_callback_aux :
  (unit -> FStarC_Getopt.parse_cmdline_res) -> unit) =
  match uu___2 with
  | (set_error_flags_callback_aux1, set_error_flags) ->
      set_error_flags_callback_aux1
let (set_error_flags : unit -> FStarC_Getopt.parse_cmdline_res) =
  match uu___2 with
  | (set_error_flags_callback_aux1, set_error_flags1) -> set_error_flags1
let (set_error_flags_callback :
  (unit -> FStarC_Getopt.parse_cmdline_res) -> unit) =
  set_error_flags_callback_aux
let (display_usage : unit -> unit) = fun uu___ -> display_usage_aux all_specs
let (fstar_bin_directory : Prims.string) =
  FStarC_Compiler_Util.get_exec_dir ()
let (file_list_ : Prims.string Prims.list FStarC_Compiler_Effect.ref) =
  FStarC_Compiler_Util.mk_ref []
let rec (parse_filename_arg :
  FStarC_Getopt.opt Prims.list ->
    Prims.bool -> Prims.string -> FStarC_Getopt.parse_cmdline_res)
  =
  fun specs1 ->
    fun enable_filenames ->
      fun arg ->
        if FStarC_Compiler_Util.starts_with arg "@"
        then
          let filename =
            FStarC_Compiler_Util.substring_from arg Prims.int_one in
          let lines = FStarC_Compiler_Util.file_get_lines filename in
          FStarC_Getopt.parse_list specs1
            (parse_filename_arg specs1 enable_filenames) lines
        else
          (if enable_filenames
           then
             (let uu___4 =
                let uu___5 = FStarC_Compiler_Effect.op_Bang file_list_ in
                FStarC_Compiler_List.op_At uu___5 [arg] in
              FStarC_Compiler_Effect.op_Colon_Equals file_list_ uu___4)
           else ();
           FStarC_Getopt.Success)
let (parse_cmd_line :
  unit -> (FStarC_Getopt.parse_cmdline_res * Prims.string Prims.list)) =
  fun uu___ ->
    let res =
      FStarC_Getopt.parse_cmdline all_specs_getopt
        (parse_filename_arg all_specs_getopt true) in
    let res1 =
      if res = FStarC_Getopt.Success then set_error_flags () else res in
    let uu___3 =
      let uu___4 = FStarC_Compiler_Effect.op_Bang file_list_ in
      FStarC_Compiler_List.map FStarC_Common.try_convert_file_name_to_mixed
        uu___4 in
    (res1, uu___3)
let (file_list : unit -> Prims.string Prims.list) =
  fun uu___ -> FStarC_Compiler_Effect.op_Bang file_list_
let (restore_cmd_line_options :
  Prims.bool -> FStarC_Getopt.parse_cmdline_res) =
  fun should_clear ->
    let old_verify_module = get_verify_module () in
    if should_clear then clear () else init ();
    (let specs1 =
       let uu___3 = specs false in
       FStarC_Compiler_List.map FStar_Pervasives_Native.fst uu___3 in
     let r =
       FStarC_Getopt.parse_cmdline specs1 (parse_filename_arg specs1 false) in
     (let uu___4 =
        let uu___5 =
          let uu___6 =
            FStarC_Compiler_List.map (fun uu___7 -> String uu___7)
              old_verify_module in
          List uu___6 in
        ("verify_module", uu___5) in
      set_option' uu___4);
     r)
let (module_name_of_file_name : Prims.string -> Prims.string) =
  fun f ->
    let f1 = FStarC_Compiler_Util.basename f in
    let f2 =
      let uu___ =
        let uu___3 =
          let uu___4 =
            let uu___5 = FStarC_Compiler_Util.get_file_extension f1 in
            FStarC_Compiler_String.length uu___5 in
          (FStarC_Compiler_String.length f1) - uu___4 in
        uu___3 - Prims.int_one in
      FStarC_Compiler_String.substring f1 Prims.int_zero uu___ in
    FStarC_Compiler_String.lowercase f2
let (should_check : Prims.string -> Prims.bool) =
  fun m ->
    let l = get_verify_module () in
    FStarC_Compiler_List.contains (FStarC_Compiler_String.lowercase m) l
let (should_verify : Prims.string -> Prims.bool) =
  fun m ->
    (let uu___ = get_lax () in Prims.op_Negation uu___) && (should_check m)
let (should_check_file : Prims.string -> Prims.bool) =
  fun fn -> let uu___ = module_name_of_file_name fn in should_check uu___
let (should_verify_file : Prims.string -> Prims.bool) =
  fun fn -> let uu___ = module_name_of_file_name fn in should_verify uu___
let (module_name_eq : Prims.string -> Prims.string -> Prims.bool) =
  fun m1 ->
    fun m2 ->
      (FStarC_Compiler_String.lowercase m1) =
        (FStarC_Compiler_String.lowercase m2)
let (should_print_message : Prims.string -> Prims.bool) =
  fun m ->
    let uu___ = should_verify m in if uu___ then m <> "Prims" else false
let (custom_prims : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu___ -> get_prims ()
let (cache_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu___ -> get_cache_dir ()
let (include_ : unit -> Prims.string Prims.list) =
  fun uu___ -> get_include ()
let (path_of_text : Prims.string -> Prims.string Prims.list) =
  fun text -> FStarC_Compiler_String.split [46] text
let (parse_settings :
  Prims.string Prims.list ->
    (Prims.string Prims.list * Prims.bool) Prims.list)
  =
  fun ns ->
    let cache = FStarC_Compiler_Util.smap_create (Prims.of_int (31)) in
    let with_cache f s =
      let uu___ = FStarC_Compiler_Util.smap_try_find cache s in
      match uu___ with
      | FStar_Pervasives_Native.Some s1 -> s1
      | FStar_Pervasives_Native.None ->
          let res = f s in (FStarC_Compiler_Util.smap_add cache s res; res) in
    let parse_one_setting s =
      if s = "*"
      then ([], true)
      else
        if s = "-*"
        then ([], false)
        else
          if FStarC_Compiler_Util.starts_with s "-"
          then
            (let path =
               let uu___4 =
                 FStarC_Compiler_Util.substring_from s Prims.int_one in
               path_of_text uu___4 in
             (path, false))
          else
            (let s1 =
               if FStarC_Compiler_Util.starts_with s "+"
               then FStarC_Compiler_Util.substring_from s Prims.int_one
               else s in
             ((path_of_text s1), true)) in
    let uu___ =
      FStarC_Compiler_List.collect
        (fun s ->
           let s1 = FStarC_Compiler_Util.trim_string s in
           if s1 = ""
           then []
           else
             with_cache
               (fun s2 ->
                  let s3 = FStarC_Compiler_Util.replace_char s2 32 44 in
                  let uu___4 =
                    let uu___5 =
                      FStarC_Compiler_List.concatMap
                        (fun s4 -> FStarC_Compiler_Util.split s4 ",")
                        (FStarC_Compiler_Util.splitlines s3) in
                    FStarC_Compiler_List.filter (fun s4 -> s4 <> "") uu___5 in
                  FStarC_Compiler_List.map parse_one_setting uu___4) s1) ns in
    FStarC_Compiler_List.rev uu___
let (admit_smt_queries : unit -> Prims.bool) =
  fun uu___ -> get_admit_smt_queries ()
let (admit_except : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu___ -> get_admit_except ()
let (compat_pre_core_should_register : unit -> Prims.bool) =
  fun uu___ ->
    let uu___3 = get_compat_pre_core () in
    match uu___3 with
    | FStar_Pervasives_Native.Some uu___4 when uu___4 = Prims.int_zero ->
        false
    | uu___4 -> true
let (compat_pre_core_should_check : unit -> Prims.bool) =
  fun uu___ ->
    let uu___3 = get_compat_pre_core () in
    match uu___3 with
    | FStar_Pervasives_Native.Some uu___4 when uu___4 = Prims.int_zero ->
        false
    | FStar_Pervasives_Native.Some uu___4 when uu___4 = Prims.int_one ->
        false
    | uu___4 -> true
let (compat_pre_core_set : unit -> Prims.bool) =
  fun uu___ ->
    let uu___3 = get_compat_pre_core () in
    match uu___3 with
    | FStar_Pervasives_Native.None -> false
    | uu___4 -> true
let (compat_pre_typed_indexed_effects : unit -> Prims.bool) =
  fun uu___ -> get_compat_pre_typed_indexed_effects ()
let (disallow_unification_guards : unit -> Prims.bool) =
  fun uu___ -> get_disallow_unification_guards ()
let (cache_checked_modules : unit -> Prims.bool) =
  fun uu___ -> get_cache_checked_modules ()
let (cache_off : unit -> Prims.bool) = fun uu___ -> get_cache_off ()
let (print_cache_version : unit -> Prims.bool) =
  fun uu___ -> get_print_cache_version ()
let (cmi : unit -> Prims.bool) = fun uu___ -> get_cmi ()
let (parse_codegen :
  Prims.string -> codegen_t FStar_Pervasives_Native.option) =
  fun uu___ ->
    match uu___ with
    | "OCaml" -> FStar_Pervasives_Native.Some OCaml
    | "FSharp" -> FStar_Pervasives_Native.Some FSharp
    | "krml" -> FStar_Pervasives_Native.Some Krml
    | "Plugin" -> FStar_Pervasives_Native.Some Plugin
    | "Extension" -> FStar_Pervasives_Native.Some Extension
    | uu___3 -> FStar_Pervasives_Native.None
let (print_codegen : codegen_t -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | OCaml -> "OCaml"
    | FSharp -> "FSharp"
    | Krml -> "krml"
    | Plugin -> "Plugin"
    | Extension -> "Extension"
let (codegen : unit -> codegen_t FStar_Pervasives_Native.option) =
  fun uu___ ->
    let uu___3 = get_codegen () in
    FStarC_Compiler_Util.map_opt uu___3
      (fun s ->
         let uu___4 = parse_codegen s in FStarC_Compiler_Util.must uu___4)
let (codegen_libs : unit -> Prims.string Prims.list Prims.list) =
  fun uu___ ->
    let uu___3 = get_codegen_lib () in
    FStarC_Compiler_List.map (fun x -> FStarC_Compiler_Util.split x ".")
      uu___3
let (profile_group_by_decl : unit -> Prims.bool) =
  fun uu___ -> get_profile_group_by_decl ()
let (defensive : unit -> Prims.bool) =
  fun uu___ -> let uu___3 = get_defensive () in uu___3 <> "no"
let (defensive_error : unit -> Prims.bool) =
  fun uu___ -> let uu___3 = get_defensive () in uu___3 = "error"
let (defensive_abort : unit -> Prims.bool) =
  fun uu___ -> let uu___3 = get_defensive () in uu___3 = "abort"
let (dep : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu___ -> get_dep ()
let (detail_errors : unit -> Prims.bool) = fun uu___ -> get_detail_errors ()
let (detail_hint_replay : unit -> Prims.bool) =
  fun uu___ -> get_detail_hint_replay ()
let (any_dump_module : unit -> Prims.bool) =
  fun uu___ -> let uu___3 = get_dump_module () in Prims.uu___is_Cons uu___3
let (dump_module : Prims.string -> Prims.bool) =
  fun s ->
    let uu___ = get_dump_module () in
    FStarC_Compiler_List.existsb (module_name_eq s) uu___
let (eager_subtyping : unit -> Prims.bool) =
  fun uu___ -> get_eager_subtyping ()
let (error_contexts : unit -> Prims.bool) =
  fun uu___ -> get_error_contexts ()
let (expose_interfaces : unit -> Prims.bool) =
  fun uu___ -> get_expose_interfaces ()
let (message_format : unit -> message_format_t) =
  fun uu___ ->
    let uu___3 = get_message_format () in
    match uu___3 with
    | "human" -> Human
    | "json" -> Json
    | illegal ->
        let uu___4 =
          let uu___5 =
            FStarC_Compiler_String.op_Hat illegal
              "`. This should be impossible: `message_format` was supposed to be validated." in
          FStarC_Compiler_String.op_Hat
            "print_issue: option `message_format` was expected to be `human` or `json`, not `"
            uu___5 in
        failwith uu___4
let (force : unit -> Prims.bool) = fun uu___ -> get_force ()
let (full_context_dependency : unit -> Prims.bool) = fun uu___ -> true
let (hide_uvar_nums : unit -> Prims.bool) =
  fun uu___ -> get_hide_uvar_nums ()
let (hint_info : unit -> Prims.bool) =
  fun uu___ -> (get_hint_info ()) || (get_query_stats ())
let (hint_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu___ -> get_hint_dir ()
let (hint_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu___ -> get_hint_file ()
let (hint_file_for_src : Prims.string -> Prims.string) =
  fun src_filename ->
    let uu___ = hint_file () in
    match uu___ with
    | FStar_Pervasives_Native.Some fn -> fn
    | FStar_Pervasives_Native.None ->
        let file_name =
          let uu___3 = hint_dir () in
          match uu___3 with
          | FStar_Pervasives_Native.Some dir ->
              let uu___4 = FStarC_Compiler_Util.basename src_filename in
              FStarC_Compiler_Util.concat_dir_filename dir uu___4
          | uu___4 -> src_filename in
        FStarC_Compiler_Util.format1 "%s.hints" file_name
let (ide : unit -> Prims.bool) = fun uu___ -> get_ide ()
let (ide_id_info_off : unit -> Prims.bool) =
  fun uu___ -> get_ide_id_info_off ()
let (ide_file_name_st :
  ((Prims.string -> unit) *
    (unit -> Prims.string FStar_Pervasives_Native.option)))
  =
  let v = FStarC_Compiler_Util.mk_ref FStar_Pervasives_Native.None in
  let set1 f =
    let uu___ = FStarC_Compiler_Effect.op_Bang v in
    match uu___ with
    | FStar_Pervasives_Native.None ->
        FStarC_Compiler_Effect.op_Colon_Equals v
          (FStar_Pervasives_Native.Some f)
    | FStar_Pervasives_Native.Some uu___3 ->
        failwith "ide_file_name_st already set" in
  let get uu___ = FStarC_Compiler_Effect.op_Bang v in (set1, get)
let (set_ide_filename : Prims.string -> unit) =
  FStar_Pervasives_Native.fst ide_file_name_st
let (ide_filename : unit -> Prims.string FStar_Pervasives_Native.option) =
  FStar_Pervasives_Native.snd ide_file_name_st
let (print : unit -> Prims.bool) = fun uu___ -> get_print ()
let (print_in_place : unit -> Prims.bool) =
  fun uu___ -> get_print_in_place ()
let (initial_fuel : unit -> Prims.int) =
  fun uu___ ->
    let uu___3 = get_initial_fuel () in
    let uu___4 = get_max_fuel () in Prims.min uu___3 uu___4
let (initial_ifuel : unit -> Prims.int) =
  fun uu___ ->
    let uu___3 = get_initial_ifuel () in
    let uu___4 = get_max_ifuel () in Prims.min uu___3 uu___4
let (interactive : unit -> Prims.bool) =
  fun uu___ -> ((get_in ()) || (get_ide ())) || (get_lsp ())
let (lax : unit -> Prims.bool) = fun uu___ -> get_lax ()
let (load : unit -> Prims.string Prims.list) = fun uu___ -> get_load ()
let (load_cmxs : unit -> Prims.string Prims.list) =
  fun uu___ -> get_load_cmxs ()
let (legacy_interactive : unit -> Prims.bool) = fun uu___ -> get_in ()
let (lsp_server : unit -> Prims.bool) = fun uu___ -> get_lsp ()
let (log_queries : unit -> Prims.bool) = fun uu___ -> get_log_queries ()
let (log_failing_queries : unit -> Prims.bool) =
  fun uu___ -> get_log_failing_queries ()
let (keep_query_captions : unit -> Prims.bool) =
  fun uu___ ->
    (get_keep_query_captions ()) &&
      ((log_queries ()) || (log_failing_queries ()))
let (log_types : unit -> Prims.bool) = fun uu___ -> get_log_types ()
let (max_fuel : unit -> Prims.int) = fun uu___ -> get_max_fuel ()
let (max_ifuel : unit -> Prims.int) = fun uu___ -> get_max_ifuel ()
let (ml_ish : unit -> Prims.bool) = fun uu___ -> get_MLish ()
let (ml_ish_effect : unit -> Prims.string) = fun uu___ -> get_MLish_effect ()
let (set_ml_ish : unit -> unit) = fun uu___ -> set_option "MLish" (Bool true)
let (no_default_includes : unit -> Prims.bool) =
  fun uu___ -> get_no_default_includes ()
let (no_extract : Prims.string -> Prims.bool) =
  fun s ->
    let uu___ = get_no_extract () in
    FStarC_Compiler_List.existsb (module_name_eq s) uu___
let (normalize_pure_terms_for_extraction : unit -> Prims.bool) =
  fun uu___ -> get_normalize_pure_terms_for_extraction ()
let (no_location_info : unit -> Prims.bool) =
  fun uu___ -> get_no_location_info ()
let (no_plugins : unit -> Prims.bool) = fun uu___ -> get_no_plugins ()
let (no_smt : unit -> Prims.bool) = fun uu___ -> get_no_smt ()
let (krmloutput : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu___ -> get_krmloutput ()
let (output_dir : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu___ -> get_odir ()
let (output_deps_to : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu___ -> get_output_deps_to ()
let (ugly : unit -> Prims.bool) = fun uu___ -> get_ugly ()
let (print_bound_var_types : unit -> Prims.bool) =
  fun uu___ -> get_print_bound_var_types ()
let (print_effect_args : unit -> Prims.bool) =
  fun uu___ -> get_print_effect_args ()
let (print_expected_failures : unit -> Prims.bool) =
  fun uu___ -> get_print_expected_failures ()
let (print_implicits : unit -> Prims.bool) =
  fun uu___ -> get_print_implicits ()
let (print_real_names : unit -> Prims.bool) =
  fun uu___ -> (get_prn ()) || (get_print_full_names ())
let (print_universes : unit -> Prims.bool) =
  fun uu___ -> get_print_universes ()
let (print_z3_statistics : unit -> Prims.bool) =
  fun uu___ -> get_print_z3_statistics ()
let (proof_recovery : unit -> Prims.bool) =
  fun uu___ -> get_proof_recovery ()
let (quake_lo : unit -> Prims.int) = fun uu___ -> get_quake_lo ()
let (quake_hi : unit -> Prims.int) = fun uu___ -> get_quake_hi ()
let (quake_keep : unit -> Prims.bool) = fun uu___ -> get_quake_keep ()
let (query_cache : unit -> Prims.bool) = fun uu___ -> get_query_cache ()
let (query_stats : unit -> Prims.bool) = fun uu___ -> get_query_stats ()
let (read_checked_file : unit -> Prims.string FStar_Pervasives_Native.option)
  = fun uu___ -> get_read_checked_file ()
let (list_plugins : unit -> Prims.bool) = fun uu___ -> get_list_plugins ()
let (locate : unit -> Prims.bool) = fun uu___ -> get_locate ()
let (locate_lib : unit -> Prims.bool) = fun uu___ -> get_locate_lib ()
let (locate_ocaml : unit -> Prims.bool) = fun uu___ -> get_locate_ocaml ()
let (read_krml_file : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu___ -> get_read_krml_file ()
let (record_hints : unit -> Prims.bool) = fun uu___ -> get_record_hints ()
let (record_options : unit -> Prims.bool) =
  fun uu___ -> get_record_options ()
let (retry : unit -> Prims.bool) = fun uu___ -> get_retry ()
let (reuse_hint_for : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu___ -> get_reuse_hint_for ()
let (report_assumes : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu___ -> get_report_assumes ()
let (silent : unit -> Prims.bool) = fun uu___ -> get_silent ()
let (smt : unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu___ -> get_smt ()
let (smtencoding_elim_box : unit -> Prims.bool) =
  fun uu___ -> get_smtencoding_elim_box ()
let (smtencoding_nl_arith_native : unit -> Prims.bool) =
  fun uu___ ->
    let uu___3 = get_smtencoding_nl_arith_repr () in uu___3 = "native"
let (smtencoding_nl_arith_wrapped : unit -> Prims.bool) =
  fun uu___ ->
    let uu___3 = get_smtencoding_nl_arith_repr () in uu___3 = "wrapped"
let (smtencoding_nl_arith_default : unit -> Prims.bool) =
  fun uu___ ->
    let uu___3 = get_smtencoding_nl_arith_repr () in uu___3 = "boxwrap"
let (smtencoding_l_arith_native : unit -> Prims.bool) =
  fun uu___ ->
    let uu___3 = get_smtencoding_l_arith_repr () in uu___3 = "native"
let (smtencoding_l_arith_default : unit -> Prims.bool) =
  fun uu___ ->
    let uu___3 = get_smtencoding_l_arith_repr () in uu___3 = "boxwrap"
let (smtencoding_valid_intro : unit -> Prims.bool) =
  fun uu___ -> get_smtencoding_valid_intro ()
let (smtencoding_valid_elim : unit -> Prims.bool) =
  fun uu___ -> get_smtencoding_valid_elim ()
let (parse_split_queries :
  Prims.string -> split_queries_t FStar_Pervasives_Native.option) =
  fun s ->
    match s with
    | "no" -> FStar_Pervasives_Native.Some No
    | "on_failure" -> FStar_Pervasives_Native.Some OnFailure
    | "always" -> FStar_Pervasives_Native.Some Always
    | uu___ -> FStar_Pervasives_Native.None
let (split_queries : unit -> split_queries_t) =
  fun uu___ ->
    let uu___3 =
      let uu___4 = get_split_queries () in parse_split_queries uu___4 in
    FStarC_Compiler_Util.must uu___3
let (tactic_raw_binders : unit -> Prims.bool) =
  fun uu___ -> get_tactic_raw_binders ()
let (tactics_failhard : unit -> Prims.bool) =
  fun uu___ -> get_tactics_failhard ()
let (tactics_info : unit -> Prims.bool) = fun uu___ -> get_tactics_info ()
let (tactic_trace : unit -> Prims.bool) = fun uu___ -> get_tactic_trace ()
let (tactic_trace_d : unit -> Prims.int) = fun uu___ -> get_tactic_trace_d ()
let (tactics_nbe : unit -> Prims.bool) = fun uu___ -> get_tactics_nbe ()
let (tcnorm : unit -> Prims.bool) = fun uu___ -> get_tcnorm ()
let (timing : unit -> Prims.bool) = fun uu___ -> get_timing ()
let (trace_error : unit -> Prims.bool) = fun uu___ -> get_trace_error ()
let (unthrottle_inductives : unit -> Prims.bool) =
  fun uu___ -> get_unthrottle_inductives ()
let (unsafe_tactic_exec : unit -> Prims.bool) =
  fun uu___ -> get_unsafe_tactic_exec ()
let (use_eq_at_higher_order : unit -> Prims.bool) =
  fun uu___ -> get_use_eq_at_higher_order ()
let (use_hints : unit -> Prims.bool) = fun uu___ -> get_use_hints ()
let (use_hint_hashes : unit -> Prims.bool) =
  fun uu___ -> get_use_hint_hashes ()
let (use_native_tactics :
  unit -> Prims.string FStar_Pervasives_Native.option) =
  fun uu___ -> get_use_native_tactics ()
let (use_tactics : unit -> Prims.bool) =
  fun uu___ -> let uu___3 = get_no_tactics () in Prims.op_Negation uu___3
let (using_facts_from :
  unit -> (Prims.string Prims.list * Prims.bool) Prims.list) =
  fun uu___ ->
    let uu___3 = get_using_facts_from () in
    match uu___3 with
    | FStar_Pervasives_Native.None -> [([], true)]
    | FStar_Pervasives_Native.Some ns -> parse_settings ns
let (warn_default_effects : unit -> Prims.bool) =
  fun uu___ -> get_warn_default_effects ()
let (warn_error : unit -> Prims.string) =
  fun uu___ ->
    let uu___3 = get_warn_error () in
    FStarC_Compiler_String.concat " " uu___3
let (z3_cliopt : unit -> Prims.string Prims.list) =
  fun uu___ -> get_z3cliopt ()
let (z3_smtopt : unit -> Prims.string Prims.list) =
  fun uu___ -> get_z3smtopt ()
let (z3_refresh : unit -> Prims.bool) = fun uu___ -> get_z3refresh ()
let (z3_rlimit : unit -> Prims.int) = fun uu___ -> get_z3rlimit ()
let (z3_rlimit_factor : unit -> Prims.int) =
  fun uu___ -> get_z3rlimit_factor ()
let (z3_seed : unit -> Prims.int) = fun uu___ -> get_z3seed ()
let (z3_version : unit -> Prims.string) = fun uu___ -> get_z3version ()
let (no_positivity : unit -> Prims.bool) = fun uu___ -> get_no_positivity ()
let (use_nbe : unit -> Prims.bool) = fun uu___ -> get_use_nbe ()
let (use_nbe_for_extraction : unit -> Prims.bool) =
  fun uu___ -> get_use_nbe_for_extraction ()
let (trivial_pre_for_unannotated_effectful_fns : unit -> Prims.bool) =
  fun uu___ -> get_trivial_pre_for_unannotated_effectful_fns ()
let (debug_keys : unit -> Prims.string Prims.list) =
  fun uu___ -> lookup_opt "debug" as_comma_string_list
let (debug_all : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "debug_all" as_bool
let (debug_all_modules : unit -> Prims.bool) =
  fun uu___ -> lookup_opt "debug_all_modules" as_bool
let with_saved_options : 'a . (unit -> 'a) -> 'a =
  fun f ->
    let uu___ = let uu___3 = trace_error () in Prims.op_Negation uu___3 in
    if uu___
    then
      (push ();
       (let r =
          try
            (fun uu___4 ->
               match () with
               | () -> let uu___5 = f () in FStar_Pervasives.Inr uu___5) ()
          with | uu___4 -> FStar_Pervasives.Inl uu___4 in
        pop ();
        (match r with
         | FStar_Pervasives.Inr v -> v
         | FStar_Pervasives.Inl ex -> FStarC_Compiler_Effect.raise ex)))
    else (push (); (let retv = f () in pop (); retv))
let (module_matches_namespace_filter :
  Prims.string -> Prims.string Prims.list -> Prims.bool) =
  fun m ->
    fun filter ->
      let m1 = FStarC_Compiler_String.lowercase m in
      let setting = parse_settings filter in
      let m_components = path_of_text m1 in
      let rec matches_path m_components1 path =
        match (m_components1, path) with
        | (uu___, []) -> true
        | (m2::ms, p::ps) ->
            (m2 = (FStarC_Compiler_String.lowercase p)) &&
              (matches_path ms ps)
        | uu___ -> false in
      let uu___ =
        FStarC_Compiler_Util.try_find
          (fun uu___3 ->
             match uu___3 with
             | (path, uu___4) -> matches_path m_components path) setting in
      match uu___ with
      | FStar_Pervasives_Native.None -> false
      | FStar_Pervasives_Native.Some (uu___3, flag) -> flag
let (matches_namespace_filter_opt :
  Prims.string ->
    Prims.string Prims.list FStar_Pervasives_Native.option -> Prims.bool)
  =
  fun m ->
    fun uu___ ->
      match uu___ with
      | FStar_Pervasives_Native.None -> false
      | FStar_Pervasives_Native.Some filter ->
          module_matches_namespace_filter m filter
type parsed_extract_setting =
  {
  target_specific_settings: (codegen_t * Prims.string) Prims.list ;
  default_settings: Prims.string FStar_Pervasives_Native.option }
let (__proj__Mkparsed_extract_setting__item__target_specific_settings :
  parsed_extract_setting -> (codegen_t * Prims.string) Prims.list) =
  fun projectee ->
    match projectee with
    | { target_specific_settings; default_settings;_} ->
        target_specific_settings
let (__proj__Mkparsed_extract_setting__item__default_settings :
  parsed_extract_setting -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { target_specific_settings; default_settings;_} -> default_settings
let (print_pes : parsed_extract_setting -> Prims.string) =
  fun pes ->
    let uu___ =
      let uu___3 =
        FStarC_Compiler_List.map
          (fun uu___4 ->
             match uu___4 with
             | (tgt, s) ->
                 FStarC_Compiler_Util.format2 "(%s, %s)" (print_codegen tgt)
                   s) pes.target_specific_settings in
      FStarC_Compiler_String.concat "; " uu___3 in
    FStarC_Compiler_Util.format2
      "{ target_specific_settings = %s;\n\t\n               default_settings = %s }"
      uu___
      (match pes.default_settings with
       | FStar_Pervasives_Native.None -> "None"
       | FStar_Pervasives_Native.Some s -> s)
let (find_setting_for_target :
  codegen_t ->
    (codegen_t * Prims.string) Prims.list ->
      Prims.string FStar_Pervasives_Native.option)
  =
  fun tgt ->
    fun s ->
      let uu___ =
        FStarC_Compiler_Util.try_find
          (fun uu___3 -> match uu___3 with | (x, uu___4) -> x = tgt) s in
      match uu___ with
      | FStar_Pervasives_Native.Some (uu___3, s1) ->
          FStar_Pervasives_Native.Some s1
      | uu___3 -> FStar_Pervasives_Native.None
let (extract_settings :
  unit -> parsed_extract_setting FStar_Pervasives_Native.option) =
  let memo =
    FStarC_Compiler_Util.mk_ref (FStar_Pervasives_Native.None, false) in
  let merge_parsed_extract_settings p0 p1 =
    let merge_setting s0 s1 =
      match (s0, s1) with
      | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) ->
          FStar_Pervasives_Native.None
      | (FStar_Pervasives_Native.Some p, FStar_Pervasives_Native.None) ->
          FStar_Pervasives_Native.Some p
      | (FStar_Pervasives_Native.None, FStar_Pervasives_Native.Some p) ->
          FStar_Pervasives_Native.Some p
      | (FStar_Pervasives_Native.Some p01, FStar_Pervasives_Native.Some p11)
          ->
          let uu___ =
            let uu___3 = FStarC_Compiler_String.op_Hat "," p11 in
            FStarC_Compiler_String.op_Hat p01 uu___3 in
          FStar_Pervasives_Native.Some uu___ in
    let merge_target tgt =
      let uu___ =
        let uu___3 = find_setting_for_target tgt p0.target_specific_settings in
        let uu___4 = find_setting_for_target tgt p1.target_specific_settings in
        merge_setting uu___3 uu___4 in
      match uu___ with
      | FStar_Pervasives_Native.None -> []
      | FStar_Pervasives_Native.Some x -> [(tgt, x)] in
    let uu___ =
      FStarC_Compiler_List.collect merge_target
        [OCaml; FSharp; Krml; Plugin; Extension] in
    let uu___3 = merge_setting p0.default_settings p1.default_settings in
    { target_specific_settings = uu___; default_settings = uu___3 } in
  fun uu___ ->
    let uu___3 = FStarC_Compiler_Effect.op_Bang memo in
    match uu___3 with
    | (result, set1) ->
        let fail msg =
          display_usage ();
          (let uu___5 =
             FStarC_Compiler_Util.format1
               "Could not parse '%s' passed to the --extract option" msg in
           failwith uu___5) in
        if set1
        then result
        else
          (let uu___5 = get_extract () in
           match uu___5 with
           | FStar_Pervasives_Native.None ->
               (FStarC_Compiler_Effect.op_Colon_Equals memo
                  (FStar_Pervasives_Native.None, true);
                FStar_Pervasives_Native.None)
           | FStar_Pervasives_Native.Some extract_settings1 ->
               let parse_one_setting extract_setting =
                 let tgt_specific_settings =
                   FStarC_Compiler_Util.split extract_setting ";" in
                 let split_one t_setting =
                   match FStarC_Compiler_Util.split t_setting ":" with
                   | default_setting::[] ->
                       FStar_Pervasives.Inr
                         (FStarC_Compiler_Util.trim_string default_setting)
                   | target::setting::[] ->
                       let target1 = FStarC_Compiler_Util.trim_string target in
                       let uu___6 = parse_codegen target1 in
                       (match uu___6 with
                        | FStar_Pervasives_Native.None -> fail target1
                        | FStar_Pervasives_Native.Some tgt ->
                            FStar_Pervasives.Inl
                              (tgt,
                                (FStarC_Compiler_Util.trim_string setting))
                        | uu___7 -> fail t_setting) in
                 let settings =
                   FStarC_Compiler_List.map split_one tgt_specific_settings in
                 let fail_duplicate msg tgt =
                   display_usage ();
                   (let uu___7 =
                      FStarC_Compiler_Util.format2
                        "Could not parse '%s'; multiple setting for %s target"
                        msg tgt in
                    failwith uu___7) in
                 let pes =
                   FStarC_Compiler_List.fold_right
                     (fun setting ->
                        fun out ->
                          match setting with
                          | FStar_Pervasives.Inr def ->
                              (match out.default_settings with
                               | FStar_Pervasives_Native.None ->
                                   {
                                     target_specific_settings =
                                       (out.target_specific_settings);
                                     default_settings =
                                       (FStar_Pervasives_Native.Some def)
                                   }
                               | FStar_Pervasives_Native.Some uu___6 ->
                                   fail_duplicate def "default")
                          | FStar_Pervasives.Inl (target, setting1) ->
                              let uu___6 =
                                FStarC_Compiler_Util.try_find
                                  (fun uu___7 ->
                                     match uu___7 with
                                     | (x, uu___8) -> x = target)
                                  out.target_specific_settings in
                              (match uu___6 with
                               | FStar_Pervasives_Native.None ->
                                   {
                                     target_specific_settings =
                                       ((target, setting1) ::
                                       (out.target_specific_settings));
                                     default_settings =
                                       (out.default_settings)
                                   }
                               | FStar_Pervasives_Native.Some uu___7 ->
                                   fail_duplicate setting1
                                     (print_codegen target))) settings
                     {
                       target_specific_settings = [];
                       default_settings = FStar_Pervasives_Native.None
                     } in
                 pes in
               let empty_pes =
                 {
                   target_specific_settings = [];
                   default_settings = FStar_Pervasives_Native.None
                 } in
               let pes =
                 FStarC_Compiler_List.fold_right
                   (fun setting ->
                      fun pes1 ->
                        let uu___6 = parse_one_setting setting in
                        merge_parsed_extract_settings pes1 uu___6)
                   extract_settings1 empty_pes in
               (FStarC_Compiler_Effect.op_Colon_Equals memo
                  ((FStar_Pervasives_Native.Some pes), true);
                FStar_Pervasives_Native.Some pes))
let (should_extract : Prims.string -> codegen_t -> Prims.bool) =
  fun m ->
    fun tgt ->
      let m1 = FStarC_Compiler_String.lowercase m in
      if m1 = "prims"
      then false
      else
        (let uu___3 = extract_settings () in
         match uu___3 with
         | FStar_Pervasives_Native.Some pes ->
             ((let uu___5 =
                 let uu___6 = get_no_extract () in
                 let uu___7 = get_extract_namespace () in
                 let uu___8 = get_extract_module () in
                 (uu___6, uu___7, uu___8) in
               match uu___5 with
               | ([], [], []) -> ()
               | uu___6 ->
                   failwith
                     "Incompatible options: --extract cannot be used with --no_extract, --extract_namespace or --extract_module");
              (let tsetting =
                 let uu___5 =
                   find_setting_for_target tgt pes.target_specific_settings in
                 match uu___5 with
                 | FStar_Pervasives_Native.Some s -> s
                 | FStar_Pervasives_Native.None ->
                     (match pes.default_settings with
                      | FStar_Pervasives_Native.Some s -> s
                      | FStar_Pervasives_Native.None -> "*") in
               module_matches_namespace_filter m1 [tsetting]))
         | FStar_Pervasives_Native.None ->
             let should_extract_namespace m2 =
               let uu___4 = get_extract_namespace () in
               match uu___4 with
               | [] -> false
               | ns ->
                   FStarC_Compiler_Util.for_some
                     (fun n ->
                        FStarC_Compiler_Util.starts_with m2
                          (FStarC_Compiler_String.lowercase n)) ns in
             let should_extract_module m2 =
               let uu___4 = get_extract_module () in
               match uu___4 with
               | [] -> false
               | l ->
                   FStarC_Compiler_Util.for_some
                     (fun n -> (FStarC_Compiler_String.lowercase n) = m2) l in
             (let uu___4 = no_extract m1 in Prims.op_Negation uu___4) &&
               (let uu___4 =
                  let uu___5 = get_extract_namespace () in
                  let uu___6 = get_extract_module () in (uu___5, uu___6) in
                (match uu___4 with
                 | ([], []) -> true
                 | uu___5 ->
                     (should_extract_namespace m1) ||
                       (should_extract_module m1))))
let (should_be_already_cached : Prims.string -> Prims.bool) =
  fun m ->
    (let uu___ = should_check m in Prims.op_Negation uu___) &&
      (let uu___ = get_already_cached () in
       match uu___ with
       | FStar_Pervasives_Native.None -> false
       | FStar_Pervasives_Native.Some already_cached_setting ->
           module_matches_namespace_filter m already_cached_setting)
let (profile_enabled :
  Prims.string FStar_Pervasives_Native.option -> Prims.string -> Prims.bool)
  =
  fun modul_opt ->
    fun phase ->
      match modul_opt with
      | FStar_Pervasives_Native.None ->
          let uu___ = get_profile_component () in
          matches_namespace_filter_opt phase uu___
      | FStar_Pervasives_Native.Some modul ->
          ((let uu___ = get_profile () in
            matches_namespace_filter_opt modul uu___) &&
             (let uu___ = get_profile_component () in
              matches_namespace_filter_opt phase uu___))
            ||
            (((timing ()) &&
                (phase = "FStarC.TypeChecker.Tc.process_one_decl"))
               && (should_check modul))
exception File_argument of Prims.string 
let (uu___is_File_argument : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | File_argument uu___ -> true | uu___ -> false
let (__proj__File_argument__item__uu___ : Prims.exn -> Prims.string) =
  fun projectee -> match projectee with | File_argument uu___ -> uu___
let (set_options : Prims.string -> FStarC_Getopt.parse_cmdline_res) =
  fun s ->
    try
      (fun uu___ ->
         match () with
         | () ->
             if s = ""
             then FStarC_Getopt.Success
             else
               (let settable_specs1 =
                  FStarC_Compiler_List.map FStar_Pervasives_Native.fst
                    settable_specs in
                let res =
                  FStarC_Getopt.parse_string settable_specs1
                    (fun s1 ->
                       FStarC_Compiler_Effect.raise (File_argument s1);
                       FStarC_Getopt.Error "set_options with file argument")
                    s in
                if res = FStarC_Getopt.Success
                then set_error_flags ()
                else res)) ()
    with
    | File_argument s1 ->
        let uu___3 =
          FStarC_Compiler_Util.format1 "File %s is not a valid option" s1 in
        FStarC_Getopt.Error uu___3
let with_options : 'a . Prims.string -> (unit -> 'a) -> 'a =
  fun s ->
    fun f ->
      with_saved_options
        (fun uu___ -> (let uu___4 = set_options s in ()); f ())
let (get_vconfig : unit -> FStarC_VConfig.vconfig) =
  fun uu___ ->
    let vcfg =
      let uu___3 = get_initial_fuel () in
      let uu___4 = get_max_fuel () in
      let uu___5 = get_initial_ifuel () in
      let uu___6 = get_max_ifuel () in
      let uu___7 = get_detail_errors () in
      let uu___8 = get_detail_hint_replay () in
      let uu___9 = get_no_smt () in
      let uu___10 = get_quake_lo () in
      let uu___11 = get_quake_hi () in
      let uu___12 = get_quake_keep () in
      let uu___13 = get_retry () in
      let uu___14 = get_smtencoding_elim_box () in
      let uu___15 = get_smtencoding_nl_arith_repr () in
      let uu___16 = get_smtencoding_l_arith_repr () in
      let uu___17 = get_smtencoding_valid_intro () in
      let uu___18 = get_smtencoding_valid_elim () in
      let uu___19 = get_tcnorm () in
      let uu___20 = get_no_plugins () in
      let uu___21 = get_no_tactics () in
      let uu___22 = get_z3cliopt () in
      let uu___23 = get_z3smtopt () in
      let uu___24 = get_z3refresh () in
      let uu___25 = get_z3rlimit () in
      let uu___26 = get_z3rlimit_factor () in
      let uu___27 = get_z3seed () in
      let uu___28 = get_z3version () in
      let uu___29 = get_trivial_pre_for_unannotated_effectful_fns () in
      let uu___30 = get_reuse_hint_for () in
      {
        FStarC_VConfig.initial_fuel = uu___3;
        FStarC_VConfig.max_fuel = uu___4;
        FStarC_VConfig.initial_ifuel = uu___5;
        FStarC_VConfig.max_ifuel = uu___6;
        FStarC_VConfig.detail_errors = uu___7;
        FStarC_VConfig.detail_hint_replay = uu___8;
        FStarC_VConfig.no_smt = uu___9;
        FStarC_VConfig.quake_lo = uu___10;
        FStarC_VConfig.quake_hi = uu___11;
        FStarC_VConfig.quake_keep = uu___12;
        FStarC_VConfig.retry = uu___13;
        FStarC_VConfig.smtencoding_elim_box = uu___14;
        FStarC_VConfig.smtencoding_nl_arith_repr = uu___15;
        FStarC_VConfig.smtencoding_l_arith_repr = uu___16;
        FStarC_VConfig.smtencoding_valid_intro = uu___17;
        FStarC_VConfig.smtencoding_valid_elim = uu___18;
        FStarC_VConfig.tcnorm = uu___19;
        FStarC_VConfig.no_plugins = uu___20;
        FStarC_VConfig.no_tactics = uu___21;
        FStarC_VConfig.z3cliopt = uu___22;
        FStarC_VConfig.z3smtopt = uu___23;
        FStarC_VConfig.z3refresh = uu___24;
        FStarC_VConfig.z3rlimit = uu___25;
        FStarC_VConfig.z3rlimit_factor = uu___26;
        FStarC_VConfig.z3seed = uu___27;
        FStarC_VConfig.z3version = uu___28;
        FStarC_VConfig.trivial_pre_for_unannotated_effectful_fns = uu___29;
        FStarC_VConfig.reuse_hint_for = uu___30
      } in
    vcfg
let (set_vconfig : FStarC_VConfig.vconfig -> unit) =
  fun vcfg ->
    let option_as tag o =
      match o with
      | FStar_Pervasives_Native.None -> Unset
      | FStar_Pervasives_Native.Some s -> tag s in
    set_option "initial_fuel" (Int (vcfg.FStarC_VConfig.initial_fuel));
    set_option "max_fuel" (Int (vcfg.FStarC_VConfig.max_fuel));
    set_option "initial_ifuel" (Int (vcfg.FStarC_VConfig.initial_ifuel));
    set_option "max_ifuel" (Int (vcfg.FStarC_VConfig.max_ifuel));
    set_option "detail_errors" (Bool (vcfg.FStarC_VConfig.detail_errors));
    set_option "detail_hint_replay"
      (Bool (vcfg.FStarC_VConfig.detail_hint_replay));
    set_option "no_smt" (Bool (vcfg.FStarC_VConfig.no_smt));
    set_option "quake_lo" (Int (vcfg.FStarC_VConfig.quake_lo));
    set_option "quake_hi" (Int (vcfg.FStarC_VConfig.quake_hi));
    set_option "quake_keep" (Bool (vcfg.FStarC_VConfig.quake_keep));
    set_option "retry" (Bool (vcfg.FStarC_VConfig.retry));
    set_option "smtencoding.elim_box"
      (Bool (vcfg.FStarC_VConfig.smtencoding_elim_box));
    set_option "smtencoding.nl_arith_repr"
      (String (vcfg.FStarC_VConfig.smtencoding_nl_arith_repr));
    set_option "smtencoding.l_arith_repr"
      (String (vcfg.FStarC_VConfig.smtencoding_l_arith_repr));
    set_option "smtencoding.valid_intro"
      (Bool (vcfg.FStarC_VConfig.smtencoding_valid_intro));
    set_option "smtencoding.valid_elim"
      (Bool (vcfg.FStarC_VConfig.smtencoding_valid_elim));
    set_option "tcnorm" (Bool (vcfg.FStarC_VConfig.tcnorm));
    set_option "no_plugins" (Bool (vcfg.FStarC_VConfig.no_plugins));
    set_option "no_tactics" (Bool (vcfg.FStarC_VConfig.no_tactics));
    (let uu___22 =
       let uu___23 =
         FStarC_Compiler_List.map (fun uu___24 -> String uu___24)
           vcfg.FStarC_VConfig.z3cliopt in
       List uu___23 in
     set_option "z3cliopt" uu___22);
    (let uu___23 =
       let uu___24 =
         FStarC_Compiler_List.map (fun uu___25 -> String uu___25)
           vcfg.FStarC_VConfig.z3smtopt in
       List uu___24 in
     set_option "z3smtopt" uu___23);
    set_option "z3refresh" (Bool (vcfg.FStarC_VConfig.z3refresh));
    set_option "z3rlimit" (Int (vcfg.FStarC_VConfig.z3rlimit));
    set_option "z3rlimit_factor" (Int (vcfg.FStarC_VConfig.z3rlimit_factor));
    set_option "z3seed" (Int (vcfg.FStarC_VConfig.z3seed));
    set_option "z3version" (String (vcfg.FStarC_VConfig.z3version));
    set_option "trivial_pre_for_unannotated_effectful_fns"
      (Bool (vcfg.FStarC_VConfig.trivial_pre_for_unannotated_effectful_fns));
    (let uu___30 =
       option_as (fun uu___31 -> String uu___31)
         vcfg.FStarC_VConfig.reuse_hint_for in
     set_option "reuse_hint_for" uu___30)
let (showable_codegen_t : codegen_t FStarC_Class_Show.showable) =
  { FStarC_Class_Show.show = print_codegen }
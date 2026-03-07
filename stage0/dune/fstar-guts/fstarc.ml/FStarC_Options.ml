open Prims
let check_include_dir : (Prims.string -> unit) FStarC_Effect.ref=
  FStarC_Effect.mk_ref (fun s -> ())
exception NotSettable of Prims.string 
let uu___is_NotSettable (projectee : Prims.exn) : Prims.bool=
  match projectee with | NotSettable uu___ -> true | uu___ -> false
let __proj__NotSettable__item__uu___ (projectee : Prims.exn) : Prims.string=
  match projectee with | NotSettable uu___ -> uu___
type codegen_t =
  | OCaml 
  | FSharp 
  | Krml 
  | Plugin 
  | PluginNoLib 
  | Extension 
let uu___is_OCaml (projectee : codegen_t) : Prims.bool=
  match projectee with | OCaml -> true | uu___ -> false
let uu___is_FSharp (projectee : codegen_t) : Prims.bool=
  match projectee with | FSharp -> true | uu___ -> false
let uu___is_Krml (projectee : codegen_t) : Prims.bool=
  match projectee with | Krml -> true | uu___ -> false
let uu___is_Plugin (projectee : codegen_t) : Prims.bool=
  match projectee with | Plugin -> true | uu___ -> false
let uu___is_PluginNoLib (projectee : codegen_t) : Prims.bool=
  match projectee with | PluginNoLib -> true | uu___ -> false
let uu___is_Extension (projectee : codegen_t) : Prims.bool=
  match projectee with | Extension -> true | uu___ -> false
type split_queries_t =
  | No 
  | OnFailure 
  | Always 
let uu___is_No (projectee : split_queries_t) : Prims.bool=
  match projectee with | No -> true | uu___ -> false
let uu___is_OnFailure (projectee : split_queries_t) : Prims.bool=
  match projectee with | OnFailure -> true | uu___ -> false
let uu___is_Always (projectee : split_queries_t) : Prims.bool=
  match projectee with | Always -> true | uu___ -> false
type message_format_t =
  | Json 
  | Human 
  | Github 
let uu___is_Json (projectee : message_format_t) : Prims.bool=
  match projectee with | Json -> true | uu___ -> false
let uu___is_Human (projectee : message_format_t) : Prims.bool=
  match projectee with | Human -> true | uu___ -> false
let uu___is_Github (projectee : message_format_t) : Prims.bool=
  match projectee with | Github -> true | uu___ -> false
type option_val =
  | Bool of Prims.bool 
  | String of Prims.string 
  | Path of Prims.string 
  | Int of Prims.int 
  | List of option_val Prims.list 
  | Unset 
let uu___is_Bool (projectee : option_val) : Prims.bool=
  match projectee with | Bool _0 -> true | uu___ -> false
let __proj__Bool__item___0 (projectee : option_val) : Prims.bool=
  match projectee with | Bool _0 -> _0
let uu___is_String (projectee : option_val) : Prims.bool=
  match projectee with | String _0 -> true | uu___ -> false
let __proj__String__item___0 (projectee : option_val) : Prims.string=
  match projectee with | String _0 -> _0
let uu___is_Path (projectee : option_val) : Prims.bool=
  match projectee with | Path _0 -> true | uu___ -> false
let __proj__Path__item___0 (projectee : option_val) : Prims.string=
  match projectee with | Path _0 -> _0
let uu___is_Int (projectee : option_val) : Prims.bool=
  match projectee with | Int _0 -> true | uu___ -> false
let __proj__Int__item___0 (projectee : option_val) : Prims.int=
  match projectee with | Int _0 -> _0
let uu___is_List (projectee : option_val) : Prims.bool=
  match projectee with | List _0 -> true | uu___ -> false
let __proj__List__item___0 (projectee : option_val) : option_val Prims.list=
  match projectee with | List _0 -> _0
let uu___is_Unset (projectee : option_val) : Prims.bool=
  match projectee with | Unset -> true | uu___ -> false
type optionstate = option_val FStarC_PSMap.t
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
let uu___is_Const (projectee : opt_type) : Prims.bool=
  match projectee with | Const _0 -> true | uu___ -> false
let __proj__Const__item___0 (projectee : opt_type) : option_val=
  match projectee with | Const _0 -> _0
let uu___is_IntStr (projectee : opt_type) : Prims.bool=
  match projectee with | IntStr _0 -> true | uu___ -> false
let __proj__IntStr__item___0 (projectee : opt_type) : Prims.string=
  match projectee with | IntStr _0 -> _0
let uu___is_BoolStr (projectee : opt_type) : Prims.bool=
  match projectee with | BoolStr -> true | uu___ -> false
let uu___is_PathStr (projectee : opt_type) : Prims.bool=
  match projectee with | PathStr _0 -> true | uu___ -> false
let __proj__PathStr__item___0 (projectee : opt_type) : Prims.string=
  match projectee with | PathStr _0 -> _0
let uu___is_SimpleStr (projectee : opt_type) : Prims.bool=
  match projectee with | SimpleStr _0 -> true | uu___ -> false
let __proj__SimpleStr__item___0 (projectee : opt_type) : Prims.string=
  match projectee with | SimpleStr _0 -> _0
let uu___is_EnumStr (projectee : opt_type) : Prims.bool=
  match projectee with | EnumStr _0 -> true | uu___ -> false
let __proj__EnumStr__item___0 (projectee : opt_type) :
  Prims.string Prims.list= match projectee with | EnumStr _0 -> _0
let uu___is_OpenEnumStr (projectee : opt_type) : Prims.bool=
  match projectee with | OpenEnumStr _0 -> true | uu___ -> false
let __proj__OpenEnumStr__item___0 (projectee : opt_type) :
  (Prims.string Prims.list * Prims.string)=
  match projectee with | OpenEnumStr _0 -> _0
let uu___is_PostProcessed (projectee : opt_type) : Prims.bool=
  match projectee with | PostProcessed _0 -> true | uu___ -> false
let __proj__PostProcessed__item___0 (projectee : opt_type) :
  ((option_val -> option_val) * opt_type)=
  match projectee with | PostProcessed _0 -> _0
let uu___is_Accumulated (projectee : opt_type) : Prims.bool=
  match projectee with | Accumulated _0 -> true | uu___ -> false
let __proj__Accumulated__item___0 (projectee : opt_type) : opt_type=
  match projectee with | Accumulated _0 -> _0
let uu___is_ReverseAccumulated (projectee : opt_type) : Prims.bool=
  match projectee with | ReverseAccumulated _0 -> true | uu___ -> false
let __proj__ReverseAccumulated__item___0 (projectee : opt_type) : opt_type=
  match projectee with | ReverseAccumulated _0 -> _0
let uu___is_WithSideEffect (projectee : opt_type) : Prims.bool=
  match projectee with | WithSideEffect _0 -> true | uu___ -> false
let __proj__WithSideEffect__item___0 (projectee : opt_type) :
  ((unit -> unit) * opt_type)= match projectee with | WithSideEffect _0 -> _0
let debug_embedding : Prims.bool FStarC_Effect.ref=
  FStarC_Effect.mk_ref false
let eager_embedding : Prims.bool FStarC_Effect.ref=
  FStarC_Effect.mk_ref false
let as_bool (uu___ : option_val) : Prims.bool=
  match uu___ with
  | Bool b -> b
  | uu___1 -> FStarC_Effect.failwith "Impos: expected Bool"
let as_int (uu___ : option_val) : Prims.int=
  match uu___ with
  | Int b -> b
  | uu___1 -> FStarC_Effect.failwith "Impos: expected Int"
let as_string (uu___ : option_val) : Prims.string=
  match uu___ with
  | String b -> b
  | Path b -> b
  | uu___1 -> FStarC_Effect.failwith "Impos: expected String"
let as_list' (uu___ : option_val) : option_val Prims.list=
  match uu___ with
  | List ts -> ts
  | uu___1 -> FStarC_Effect.failwith "Impos: expected List"
let as_list (as_t : option_val -> 'a) (x : option_val) : 'a Prims.list=
  let uu___ = as_list' x in FStarC_List.map as_t uu___
let as_option (as_t : option_val -> 'a) (uu___ : option_val) :
  'a FStar_Pervasives_Native.option=
  match uu___ with
  | Unset -> FStar_Pervasives_Native.None
  | v -> let uu___1 = as_t v in FStar_Pervasives_Native.Some uu___1
let as_comma_string_list (uu___ : option_val) : Prims.string Prims.list=
  match uu___ with
  | List ls ->
      let uu___1 =
        FStarC_List.map
          (fun l -> let uu___2 = as_string l in FStarC_Util.split uu___2 ",")
          ls in
      FStarC_List.flatten uu___1
  | uu___1 -> FStarC_Effect.failwith "Impos: expected String (comma list)"
type history1 =
  (FStarC_Debug.saved_state * FStarC_Options_Ext.ext_state * Prims.bool *
    optionstate)
let fstar_options : optionstate FStarC_Effect.ref=
  FStarC_Effect.mk_ref (FStarC_PSMap.empty ())
let snapshot_all (uu___ : unit) : history1=
  let uu___1 = FStarC_Debug.snapshot () in
  let uu___2 = FStarC_Options_Ext.save () in
  let uu___3 = FStarC_Effect.op_Bang FStarC_Stats.enabled in
  let uu___4 = FStarC_Effect.op_Bang fstar_options in
  (uu___1, uu___2, uu___3, uu___4)
let restore_all (h : history1) : unit=
  let uu___ = h in
  match uu___ with
  | (dbg, ext, stats, opts) ->
      (FStarC_Debug.restore dbg;
       FStarC_Options_Ext.restore ext;
       FStarC_Effect.op_Colon_Equals FStarC_Stats.enabled stats;
       FStarC_Effect.op_Colon_Equals fstar_options opts)
let history : history1 Prims.list Prims.list FStarC_Effect.ref=
  FStarC_Effect.mk_ref []
let peek (uu___ : unit) : optionstate= FStarC_Effect.op_Bang fstar_options
let internal_push (uu___ : unit) : unit=
  let uu___1 = FStarC_Effect.op_Bang history in
  match uu___1 with
  | lev1::rest ->
      let newhd = snapshot_all () in
      FStarC_Effect.op_Colon_Equals history ((newhd :: lev1) :: rest)
let internal_pop (uu___ : unit) : Prims.bool=
  let uu___1 = FStarC_Effect.op_Bang history in
  match uu___1 with
  | lev1::rest ->
      (match lev1 with
       | [] -> false
       | snap::lev1' ->
           (restore_all snap;
            FStarC_Effect.op_Colon_Equals history (lev1' :: rest);
            true))
let push (uu___ : unit) : unit=
  internal_push ();
  (let uu___2 = FStarC_Effect.op_Bang history in
   match uu___2 with
   | lev1::uu___3 ->
       ((let uu___5 =
           let uu___6 = FStarC_Effect.op_Bang history in lev1 :: uu___6 in
         FStarC_Effect.op_Colon_Equals history uu___5);
        (let uu___6 = internal_pop () in ())))
let pop (uu___ : unit) : unit=
  let uu___1 = FStarC_Effect.op_Bang history in
  match uu___1 with
  | [] -> FStarC_Effect.failwith "TOO MANY POPS!"
  | uu___2::levs ->
      (FStarC_Effect.op_Colon_Equals history levs;
       (let uu___4 = let uu___5 = internal_pop () in Prims.op_Negation uu___5 in
        if uu___4 then FStarC_Effect.failwith "aaa!!!" else ()))
let set (o : optionstate) : unit=
  FStarC_Effect.op_Colon_Equals fstar_options o
let depth (uu___ : unit) : Prims.int=
  let uu___1 = FStarC_Effect.op_Bang history in
  match uu___1 with | lev::uu___2 -> FStarC_List.length lev
let snapshot (uu___ : unit) : (Prims.int * unit)=
  FStarC_Common.snapshot "Options" push history ()
let rollback (depth1 : Prims.int FStar_Pervasives_Native.option) : unit=
  FStarC_Common.rollback "Options" pop history depth1
let set_option (k : Prims.string) (v : option_val) : unit=
  let map = peek () in
  if k = "report_assumes"
  then
    match FStarC_PSMap.try_find map k with
    | FStar_Pervasives_Native.Some (String "error") -> ()
    | uu___ ->
        FStarC_Effect.op_Colon_Equals fstar_options
          (FStarC_PSMap.add map k v)
  else FStarC_Effect.op_Colon_Equals fstar_options (FStarC_PSMap.add map k v)
let set_option' (uu___ : (Prims.string * option_val)) : unit=
  match uu___ with | (k, v) -> set_option k v
let set_admit_smt_queries (b : Prims.bool) : unit=
  set_option "admit_smt_queries" (Bool b)
let defaults : (Prims.string * option_val) Prims.list=
  [("abort_on", (Int Prims.int_zero));
  ("admit_except", Unset);
  ("admit_smt_queries", (Bool false));
  ("already_cached", Unset);
  ("cache_checked_modules", (Bool false));
  ("cache_off", (Bool false));
  ("no_cmi", (Bool false));
  ("codegen-lib", (List []));
  ("codegen", Unset);
  ("compat_pre_core", Unset);
  ("compat_pre_typed_indexed_effects", (Bool false));
  ("debug_all", (Bool false));
  ("debug_all_modules", (Bool false));
  ("debug", (List []));
  ("defensive", (String "no"));
  ("dep", Unset);
  ("detail_errors", (Bool false));
  ("detail_hint_replay", (Bool false));
  ("disallow_unification_guards", (Bool false));
  ("dump_ast", (Bool false));
  ("dump_module", (List []));
  ("eager_subtyping", (Bool false));
  ("error_contexts", (Bool false));
  ("expand_include", Unset);
  ("expose_interfaces", (Bool false));
  ("extract_all", (Bool false));
  ("extract_module", (List []));
  ("extract_namespace", (List []));
  ("extract", Unset);
  ("ext", Unset);
  ("force", (Bool false));
  ("fuel", Unset);
  ("help", (Bool false));
  ("hide_uvar_nums", (Bool false));
  ("hint_dir", Unset);
  ("hint_file", Unset);
  ("hint_hook", Unset);
  ("hint_info", (Bool false));
  ("ide", (Bool false));
  ("ide_id_info_off", (Bool false));
  ("ifuel", Unset);
  ("include", (List []));
  ("initial_fuel", (Int (Prims.of_int (2))));
  ("initial_ifuel", (Int Prims.int_one));
  ("keep_query_captions", (Bool true));
  ("krmloutput", Unset);
  ("lang_extensions", (List []));
  ("lax", (Bool false));
  ("list_plugins", (Bool false));
  ("load_cmxs", (List []));
  ("load", (List []));
  ("locate", (Bool false));
  ("locate_file", Unset);
  ("locate_lib", (Bool false));
  ("locate_ocaml", (Bool false));
  ("locate_z3", Unset);
  ("log_failing_queries", (Bool false));
  ("log_queries", (Bool false));
  ("log_types", (Bool false));
  ("max_fuel", (Int (Prims.of_int (8))));
  ("max_ifuel", (Int (Prims.of_int (2))));
  ("message_format", (String "auto"));
  ("no_extract", (List []));
  ("no_location_info", (Bool false));
  ("no_plugins", (Bool false));
  ("__no_positivity", (Bool false));
  ("no_prelude", (Bool false));
  ("normalize_pure_terms_for_extraction", (Bool false));
  ("no_smt", (Bool false));
  ("no_tactics", (Bool false));
  ("output_deps_to", Unset);
  ("output_to", Unset);
  ("pretype", (Bool true));
  ("prims_ref", Unset);
  ("prims", Unset);
  ("print", (Bool false));
  ("print_bound_var_types", (Bool false));
  ("print_cache_version", (Bool false));
  ("print_effect_args", (Bool false));
  ("print_expected_failures", (Bool false));
  ("print_full_names", (Bool false));
  ("print_implicits", (Bool false));
  ("print_in_place", (Bool false));
  ("print_universes", (Bool false));
  ("print_z3_statistics", (Bool false));
  ("prn", (Bool false));
  ("profile_component", Unset);
  ("profile_group_by_decl", (Bool false));
  ("profile", Unset);
  ("proof_recovery", (Bool false));
  ("quake_hi", (Int Prims.int_one));
  ("quake", (Int Prims.int_zero));
  ("quake_keep", (Bool false));
  ("quake_lo", (Int Prims.int_one));
  ("query_cache", (Bool false));
  ("query_stats", (Bool false));
  ("read_checked_file", Unset);
  ("read_krml_file", Unset);
  ("record_hints", (Bool false));
  ("record_options", (Bool false));
  ("report_assumes", Unset);
  ("retry", (Bool false));
  ("reuse_hint_for", Unset);
  ("silent", (Bool false));
  ("smtencoding.elim_box", (Bool false));
  ("smtencoding.l_arith_repr", (String "boxwrap"));
  ("smtencoding.nl_arith_repr", (String "boxwrap"));
  ("smtencoding.valid_elim", (Bool false));
  ("smtencoding.valid_intro", (Bool true));
  ("smt", Unset);
  ("split_queries", (String "on_failure"));
  ("stats", (Bool false));
  ("tactic_raw_binders", (Bool false));
  ("tactics_failhard", (Bool false));
  ("tactics_info", (Bool false));
  ("__tactics_nbe", (Bool false));
  ("tactic_trace", (Bool false));
  ("tactic_trace_d", (Int Prims.int_zero));
  ("tcnorm", (Bool true));
  ("timing", (Bool false));
  ("trace_error", (Bool false));
  ("trivial_pre_for_unannotated_effectful_fns", (Bool true));
  ("ugly", (Bool false));
  ("unsafe_tactic_exec", (Bool false));
  ("unthrottle_inductives", (Bool false));
  ("use_eq_at_higher_order", (Bool false));
  ("use_hint_hashes", (Bool false));
  ("use_hints", (Bool false));
  ("use_native_tactics", Unset);
  ("use_nbe", (Bool false));
  ("use_nbe_for_extraction", (Bool false));
  ("using_facts_from", Unset);
  ("verify_module", (List []));
  ("warn_default_effects", (Bool false));
  ("warn_error", (List []));
  ("z3cliopt", (List []));
  ("z3refresh", (Bool false));
  ("z3rlimit_factor", (Int Prims.int_one));
  ("z3rlimit", (Int (Prims.of_int (5))));
  ("z3seed", (Int Prims.int_zero));
  ("z3smtopt", (List []));
  ("z3version", (String "4.13.3"))]
let init (uu___ : unit) : unit=
  FStarC_Debug.disable_all ();
  FStarC_Options_Ext.reset ();
  FStarC_Effect.op_Colon_Equals fstar_options (FStarC_PSMap.empty ());
  FStarC_List.iter set_option' defaults
let clear (uu___ : unit) : unit=
  FStarC_Effect.op_Colon_Equals history [[]]; init ()
let uu___0 : unit= clear ()
let get_option (s : Prims.string) : option_val=
  let uu___ = let uu___1 = peek () in FStarC_PSMap.try_find uu___1 s in
  match uu___ with
  | FStar_Pervasives_Native.None ->
      FStarC_Effect.failwith
        (FStarC_String.op_Hat "Impossible: option "
           (FStarC_String.op_Hat s " not found"))
  | FStar_Pervasives_Native.Some s1 -> s1
let rec option_val_to_string (v : option_val) : Prims.string=
  match v with
  | Bool b ->
      let uu___ = FStarC_Class_Show.show FStarC_Class_Show.showable_bool b in
      FStarC_String.op_Hat "Bool " uu___
  | String s ->
      let uu___ = FStarC_Class_Show.show FStarC_Class_Show.showable_string s in
      FStarC_String.op_Hat "String " uu___
  | Path s ->
      let uu___ = FStarC_Class_Show.show FStarC_Class_Show.showable_string s in
      FStarC_String.op_Hat "Path " uu___
  | Int i ->
      let uu___ = FStarC_Class_Show.show FStarC_Class_Show.showable_int i in
      FStarC_String.op_Hat "Int " uu___
  | List vs ->
      let uu___ = FStarC_Common.string_of_list option_val_to_string vs in
      FStarC_String.op_Hat "List " uu___
  | Unset -> "Unset"
let showable_option_val : option_val FStarC_Class_Show.showable=
  { FStarC_Class_Show.show = option_val_to_string }
let rec eq_option_val (v1 : option_val) (v2 : option_val) : Prims.bool=
  match (v1, v2) with
  | (Bool x1, Bool x2) ->
      FStarC_Class_Deq.op_Equals_Question FStarC_Class_Deq.deq_bool x1 x2
  | (String x1, String x2) ->
      FStarC_Class_Deq.op_Equals_Question FStarC_Class_Deq.deq_string x1 x2
  | (Path x1, Path x2) ->
      FStarC_Class_Deq.op_Equals_Question FStarC_Class_Deq.deq_string x1 x2
  | (Int x1, Int x2) ->
      FStarC_Class_Deq.op_Equals_Question FStarC_Class_Deq.deq_int x1 x2
  | (Unset, Unset) -> true
  | (List x1, List x2) -> FStarC_Common.eq_list eq_option_val x1 x2
  | (uu___, uu___1) -> false
let deq_option_val : option_val FStarC_Class_Deq.deq=
  { FStarC_Class_Deq.op_Equals_Question = eq_option_val }
let rec list_try_find :
  'a 'b .
    'a FStarC_Class_Deq.deq ->
      'a -> ('a * 'b) Prims.list -> 'b FStar_Pervasives_Native.option
  =
  fun uu___ k l ->
    match l with
    | [] -> FStar_Pervasives_Native.None
    | (k', v')::l' ->
        let uu___1 = FStarC_Class_Deq.op_Equals_Question uu___ k k' in
        if uu___1
        then FStar_Pervasives_Native.Some v'
        else list_try_find uu___ k l'
let show_options (uu___ : unit) : Prims.string=
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
                         FStar_Pervasives_Native.__proj__Some__item__v
                           (FStarC_PSMap.try_find s k) in
                       let v0 =
                         list_try_find FStarC_Class_Deq.deq_string k defaults in
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
    | String s1 -> FStarC_String.op_Hat "\"" (FStarC_String.op_Hat s1 "\"")
    | Bool b -> FStarC_Class_Show.show FStarC_Class_Show.showable_bool b
    | Int i -> FStarC_Class_Show.show FStarC_Class_Show.showable_int i
    | Path s1 -> s1
    | List s1 ->
        let uu___1 = FStarC_List.map show_optionval s1 in
        FStarC_String.concat "," uu___1
    | Unset -> "<unset>" in
  let show1 uu___1 =
    match uu___1 with
    | (k, v) ->
        let uu___2 = show_optionval v in
        FStarC_Format.fmt2 "--%s %s" k uu___2 in
  let uu___1 = FStarC_List.map show1 kvs in FStarC_String.concat "\n" uu___1
let set_verification_options (o : optionstate) : unit=
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
  FStarC_List.iter
    (fun k ->
       set_option k
         (FStar_Pervasives_Native.__proj__Some__item__v
            (FStarC_PSMap.try_find o k))) verifopts
let lookup_opt (s : Prims.string) (c : option_val -> 'a) : 'a=
  let uu___ = get_option s in c uu___
let get_abort_on (uu___ : unit) : Prims.int= lookup_opt "abort_on" as_int
let get_admit_smt_queries (uu___ : unit) : Prims.bool=
  lookup_opt "admit_smt_queries" as_bool
let get_admit_except (uu___ : unit) :
  Prims.string FStar_Pervasives_Native.option=
  lookup_opt "admit_except" (as_option as_string)
let get_compat_pre_core (uu___ : unit) :
  Prims.int FStar_Pervasives_Native.option=
  lookup_opt "compat_pre_core" (as_option as_int)
let get_compat_pre_typed_indexed_effects (uu___ : unit) : Prims.bool=
  lookup_opt "compat_pre_typed_indexed_effects" as_bool
let get_disallow_unification_guards (uu___ : unit) : Prims.bool=
  lookup_opt "disallow_unification_guards" as_bool
let get_already_cached (uu___ : unit) :
  Prims.string Prims.list FStar_Pervasives_Native.option=
  lookup_opt "already_cached" (as_option (as_list as_string))
let get_cache_checked_modules (uu___ : unit) : Prims.bool=
  lookup_opt "cache_checked_modules" as_bool
let get_cache_off (uu___ : unit) : Prims.bool= lookup_opt "cache_off" as_bool
let get_print_cache_version (uu___ : unit) : Prims.bool=
  lookup_opt "print_cache_version" as_bool
let get_no_cmi (uu___ : unit) : Prims.bool= lookup_opt "no_cmi" as_bool
let get_codegen (uu___ : unit) : Prims.string FStar_Pervasives_Native.option=
  lookup_opt "codegen" (as_option as_string)
let get_codegen_lib (uu___ : unit) : Prims.string Prims.list=
  lookup_opt "codegen-lib" (as_list as_string)
let get_defensive (uu___ : unit) : Prims.string=
  lookup_opt "defensive" as_string
let get_dep (uu___ : unit) : Prims.string FStar_Pervasives_Native.option=
  lookup_opt "dep" (as_option as_string)
let get_detail_errors (uu___ : unit) : Prims.bool=
  lookup_opt "detail_errors" as_bool
let get_detail_hint_replay (uu___ : unit) : Prims.bool=
  lookup_opt "detail_hint_replay" as_bool
let get_dump_ast (uu___ : unit) : Prims.bool= lookup_opt "dump_ast" as_bool
let get_dump_module (uu___ : unit) : Prims.string Prims.list=
  lookup_opt "dump_module" (as_list as_string)
let get_eager_subtyping (uu___ : unit) : Prims.bool=
  lookup_opt "eager_subtyping" as_bool
let get_error_contexts (uu___ : unit) : Prims.bool=
  lookup_opt "error_contexts" as_bool
let get_expose_interfaces (uu___ : unit) : Prims.bool=
  lookup_opt "expose_interfaces" as_bool
let get_message_format (uu___ : unit) : Prims.string=
  lookup_opt "message_format" as_string
let get_extract (uu___ : unit) :
  Prims.string Prims.list FStar_Pervasives_Native.option=
  lookup_opt "extract" (as_option (as_list as_string))
let get_extract_module (uu___ : unit) : Prims.string Prims.list=
  lookup_opt "extract_module" (as_list as_string)
let get_extract_namespace (uu___ : unit) : Prims.string Prims.list=
  lookup_opt "extract_namespace" (as_list as_string)
let get_force (uu___ : unit) : Prims.bool= lookup_opt "force" as_bool
let get_help (uu___ : unit) : Prims.bool= lookup_opt "help" as_bool
let get_hide_uvar_nums (uu___ : unit) : Prims.bool=
  lookup_opt "hide_uvar_nums" as_bool
let get_hint_info (uu___ : unit) : Prims.bool= lookup_opt "hint_info" as_bool
let get_hint_dir (uu___ : unit) :
  Prims.string FStar_Pervasives_Native.option=
  lookup_opt "hint_dir" (as_option as_string)
let get_hint_file (uu___ : unit) :
  Prims.string FStar_Pervasives_Native.option=
  lookup_opt "hint_file" (as_option as_string)
let get_ide (uu___ : unit) : Prims.bool= lookup_opt "ide" as_bool
let get_ide_id_info_off (uu___ : unit) : Prims.bool=
  lookup_opt "ide_id_info_off" as_bool
let get_print (uu___ : unit) : Prims.bool= lookup_opt "print" as_bool
let get_print_in_place (uu___ : unit) : Prims.bool=
  lookup_opt "print_in_place" as_bool
let get_initial_fuel (uu___ : unit) : Prims.int=
  lookup_opt "initial_fuel" as_int
let get_initial_ifuel (uu___ : unit) : Prims.int=
  lookup_opt "initial_ifuel" as_int
let get_keep_query_captions (uu___ : unit) : Prims.bool=
  lookup_opt "keep_query_captions" as_bool
let get_lang_extensions (uu___ : unit) : Prims.string Prims.list=
  lookup_opt "lang_extensions" (as_list as_string)
let get_lax (uu___ : unit) : Prims.bool= lookup_opt "lax" as_bool
let get_load (uu___ : unit) : Prims.string Prims.list=
  lookup_opt "load" (as_list as_string)
let get_load_cmxs (uu___ : unit) : Prims.string Prims.list=
  lookup_opt "load_cmxs" (as_list as_string)
let get_log_queries (uu___ : unit) : Prims.bool=
  lookup_opt "log_queries" as_bool
let get_log_failing_queries (uu___ : unit) : Prims.bool=
  lookup_opt "log_failing_queries" as_bool
let get_log_types (uu___ : unit) : Prims.bool= lookup_opt "log_types" as_bool
let get_max_fuel (uu___ : unit) : Prims.int= lookup_opt "max_fuel" as_int
let get_max_ifuel (uu___ : unit) : Prims.int= lookup_opt "max_ifuel" as_int
let get_no_extract (uu___ : unit) : Prims.string Prims.list=
  lookup_opt "no_extract" (as_list as_string)
let get_no_location_info (uu___ : unit) : Prims.bool=
  lookup_opt "no_location_info" as_bool
let get_no_prelude (uu___ : unit) : Prims.bool=
  lookup_opt "no_prelude" as_bool
let get_no_plugins (uu___ : unit) : Prims.bool=
  lookup_opt "no_plugins" as_bool
let get_no_smt (uu___ : unit) : Prims.bool= lookup_opt "no_smt" as_bool
let get_normalize_pure_terms_for_extraction (uu___ : unit) : Prims.bool=
  lookup_opt "normalize_pure_terms_for_extraction" as_bool
let get_output_to (uu___ : unit) :
  Prims.string FStar_Pervasives_Native.option=
  lookup_opt "output_to" (as_option as_string)
let get_krmloutput (uu___ : unit) :
  Prims.string FStar_Pervasives_Native.option=
  lookup_opt "krmloutput" (as_option as_string)
let get_output_deps_to (uu___ : unit) :
  Prims.string FStar_Pervasives_Native.option=
  lookup_opt "output_deps_to" (as_option as_string)
let get_ugly (uu___ : unit) : Prims.bool= lookup_opt "ugly" as_bool
let get_prims (uu___ : unit) : Prims.string FStar_Pervasives_Native.option=
  lookup_opt "prims" (as_option as_string)
let get_print_bound_var_types (uu___ : unit) : Prims.bool=
  lookup_opt "print_bound_var_types" as_bool
let get_print_effect_args (uu___ : unit) : Prims.bool=
  lookup_opt "print_effect_args" as_bool
let get_print_expected_failures (uu___ : unit) : Prims.bool=
  lookup_opt "print_expected_failures" as_bool
let get_print_full_names (uu___ : unit) : Prims.bool=
  lookup_opt "print_full_names" as_bool
let get_print_implicits (uu___ : unit) : Prims.bool=
  lookup_opt "print_implicits" as_bool
let get_print_universes (uu___ : unit) : Prims.bool=
  lookup_opt "print_universes" as_bool
let get_print_z3_statistics (uu___ : unit) : Prims.bool=
  lookup_opt "print_z3_statistics" as_bool
let get_prn (uu___ : unit) : Prims.bool= lookup_opt "prn" as_bool
let get_proof_recovery (uu___ : unit) : Prims.bool=
  lookup_opt "proof_recovery" as_bool
let get_quake_lo (uu___ : unit) : Prims.int= lookup_opt "quake_lo" as_int
let get_quake_hi (uu___ : unit) : Prims.int= lookup_opt "quake_hi" as_int
let get_quake_keep (uu___ : unit) : Prims.bool=
  lookup_opt "quake_keep" as_bool
let get_query_cache (uu___ : unit) : Prims.bool=
  lookup_opt "query_cache" as_bool
let get_query_stats (uu___ : unit) : Prims.bool=
  lookup_opt "query_stats" as_bool
let get_read_checked_file (uu___ : unit) :
  Prims.string FStar_Pervasives_Native.option=
  lookup_opt "read_checked_file" (as_option as_string)
let get_read_krml_file (uu___ : unit) :
  Prims.string FStar_Pervasives_Native.option=
  lookup_opt "read_krml_file" (as_option as_string)
let get_list_plugins (uu___ : unit) : Prims.bool=
  lookup_opt "list_plugins" as_bool
let get_locate (uu___ : unit) : Prims.bool= lookup_opt "locate" as_bool
let get_locate_lib (uu___ : unit) : Prims.bool=
  lookup_opt "locate_lib" as_bool
let get_locate_ocaml (uu___ : unit) : Prims.bool=
  lookup_opt "locate_ocaml" as_bool
let get_locate_file (uu___ : unit) :
  Prims.string FStar_Pervasives_Native.option=
  lookup_opt "locate_file" (as_option as_string)
let get_expand_include (uu___ : unit) :
  Prims.string FStar_Pervasives_Native.option=
  lookup_opt "expand_include" (as_option as_string)
let get_locate_z3 (uu___ : unit) :
  Prims.string FStar_Pervasives_Native.option=
  lookup_opt "locate_z3" (as_option as_string)
let get_record_hints (uu___ : unit) : Prims.bool=
  lookup_opt "record_hints" as_bool
let get_record_options (uu___ : unit) : Prims.bool=
  lookup_opt "record_options" as_bool
let get_retry (uu___ : unit) : Prims.bool= lookup_opt "retry" as_bool
let get_reuse_hint_for (uu___ : unit) :
  Prims.string FStar_Pervasives_Native.option=
  lookup_opt "reuse_hint_for" (as_option as_string)
let get_report_assumes (uu___ : unit) :
  Prims.string FStar_Pervasives_Native.option=
  lookup_opt "report_assumes" (as_option as_string)
let get_silent (uu___ : unit) : Prims.bool= lookup_opt "silent" as_bool
let get_smt (uu___ : unit) : Prims.string FStar_Pervasives_Native.option=
  lookup_opt "smt" (as_option as_string)
let get_smtencoding_elim_box (uu___ : unit) : Prims.bool=
  lookup_opt "smtencoding.elim_box" as_bool
let get_smtencoding_nl_arith_repr (uu___ : unit) : Prims.string=
  lookup_opt "smtencoding.nl_arith_repr" as_string
let get_smtencoding_l_arith_repr (uu___ : unit) : Prims.string=
  lookup_opt "smtencoding.l_arith_repr" as_string
let get_smtencoding_valid_intro (uu___ : unit) : Prims.bool=
  lookup_opt "smtencoding.valid_intro" as_bool
let get_smtencoding_valid_elim (uu___ : unit) : Prims.bool=
  lookup_opt "smtencoding.valid_elim" as_bool
let get_split_queries (uu___ : unit) : Prims.string=
  lookup_opt "split_queries" as_string
let get_stats (uu___ : unit) : Prims.bool= lookup_opt "stats" as_bool
let get_tactic_raw_binders (uu___ : unit) : Prims.bool=
  lookup_opt "tactic_raw_binders" as_bool
let get_tactics_failhard (uu___ : unit) : Prims.bool=
  lookup_opt "tactics_failhard" as_bool
let get_tactics_info (uu___ : unit) : Prims.bool=
  lookup_opt "tactics_info" as_bool
let get_tactic_trace (uu___ : unit) : Prims.bool=
  lookup_opt "tactic_trace" as_bool
let get_tactic_trace_d (uu___ : unit) : Prims.int=
  lookup_opt "tactic_trace_d" as_int
let get_tactics_nbe (uu___ : unit) : Prims.bool=
  lookup_opt "__tactics_nbe" as_bool
let get_tcnorm (uu___ : unit) : Prims.bool= lookup_opt "tcnorm" as_bool
let get_timing (uu___ : unit) : Prims.bool= lookup_opt "timing" as_bool
let get_trace_error (uu___ : unit) : Prims.bool=
  lookup_opt "trace_error" as_bool
let get_unthrottle_inductives (uu___ : unit) : Prims.bool=
  lookup_opt "unthrottle_inductives" as_bool
let get_unsafe_tactic_exec (uu___ : unit) : Prims.bool=
  lookup_opt "unsafe_tactic_exec" as_bool
let get_use_eq_at_higher_order (uu___ : unit) : Prims.bool=
  lookup_opt "use_eq_at_higher_order" as_bool
let get_use_hints (uu___ : unit) : Prims.bool= lookup_opt "use_hints" as_bool
let get_use_hint_hashes (uu___ : unit) : Prims.bool=
  lookup_opt "use_hint_hashes" as_bool
let get_use_native_tactics (uu___ : unit) :
  Prims.string FStar_Pervasives_Native.option=
  lookup_opt "use_native_tactics" (as_option as_string)
let get_no_tactics (uu___ : unit) : Prims.bool=
  lookup_opt "no_tactics" as_bool
let get_using_facts_from (uu___ : unit) :
  Prims.string Prims.list FStar_Pervasives_Native.option=
  lookup_opt "using_facts_from" (as_option (as_list as_string))
let get_verify_module (uu___ : unit) : Prims.string Prims.list=
  lookup_opt "verify_module" (as_list as_string)
let get_version (uu___ : unit) : Prims.bool= lookup_opt "version" as_bool
let get_warn_default_effects (uu___ : unit) : Prims.bool=
  lookup_opt "warn_default_effects" as_bool
let get_z3cliopt (uu___ : unit) : Prims.string Prims.list=
  lookup_opt "z3cliopt" (as_list as_string)
let get_z3smtopt (uu___ : unit) : Prims.string Prims.list=
  lookup_opt "z3smtopt" (as_list as_string)
let get_z3refresh (uu___ : unit) : Prims.bool= lookup_opt "z3refresh" as_bool
let get_z3rlimit (uu___ : unit) : Prims.int= lookup_opt "z3rlimit" as_int
let get_z3rlimit_factor (uu___ : unit) : Prims.int=
  lookup_opt "z3rlimit_factor" as_int
let get_z3seed (uu___ : unit) : Prims.int= lookup_opt "z3seed" as_int
let get_z3version (uu___ : unit) : Prims.string=
  lookup_opt "z3version" as_string
let get_no_positivity (uu___ : unit) : Prims.bool=
  lookup_opt "__no_positivity" as_bool
let get_warn_error (uu___ : unit) : Prims.string Prims.list=
  lookup_opt "warn_error" (as_list as_string)
let get_use_nbe (uu___ : unit) : Prims.bool= lookup_opt "use_nbe" as_bool
let get_use_nbe_for_extraction (uu___ : unit) : Prims.bool=
  lookup_opt "use_nbe_for_extraction" as_bool
let get_trivial_pre_for_unannotated_effectful_fns (uu___ : unit) :
  Prims.bool= lookup_opt "trivial_pre_for_unannotated_effectful_fns" as_bool
let get_profile (uu___ : unit) :
  Prims.string Prims.list FStar_Pervasives_Native.option=
  lookup_opt "profile" (as_option (as_list as_string))
let get_profile_group_by_decl (uu___ : unit) : Prims.bool=
  lookup_opt "profile_group_by_decl" as_bool
let get_profile_component (uu___ : unit) :
  Prims.string Prims.list FStar_Pervasives_Native.option=
  lookup_opt "profile_component" (as_option (as_list as_string))
let _version : Prims.string FStarC_Effect.ref= FStarC_Effect.mk_ref ""
let _platform : Prims.string FStarC_Effect.ref= FStarC_Effect.mk_ref ""
let _compiler : Prims.string FStarC_Effect.ref= FStarC_Effect.mk_ref ""
let _date : Prims.string FStarC_Effect.ref= FStarC_Effect.mk_ref " not set"
let _commit : Prims.string FStarC_Effect.ref= FStarC_Effect.mk_ref ""
let display_version (uu___ : unit) : unit=
  let uu___1 =
    let uu___2 = FStarC_Effect.op_Bang _version in
    let uu___3 = FStarC_Effect.op_Bang _platform in
    let uu___4 =
      FStarC_Class_Show.show FStarC_Platform.showable_sys
        FStarC_Platform_Base.system in
    let uu___5 = FStarC_Effect.op_Bang _compiler in
    let uu___6 = FStarC_Effect.op_Bang _date in
    let uu___7 = FStarC_Effect.op_Bang _commit in
    FStarC_Format.fmt6
      "F* %s\nplatform=%s\nsystem=%s\ncompiler=%s\ndate=%s\ncommit=%s\n"
      uu___2 uu___3 uu___4 uu___5 uu___6 uu___7 in
  FStarC_Format.print_string uu___1
let bold_doc (d : FStar_Pprint.document) : FStar_Pprint.document=
  let uu___ =
    let uu___1 = FStarC_Format.stdout_isatty () in
    uu___1 = (FStar_Pervasives_Native.Some true) in
  if uu___
  then
    FStar_Pprint.op_Hat_Hat
      (FStar_Pprint.fancystring "\027[39;1m" Prims.int_zero)
      (FStar_Pprint.op_Hat_Hat d
         (FStar_Pprint.fancystring "\027[0m" Prims.int_zero))
  else d
let display_debug_keys (uu___ : unit) : unit=
  let keys = FStarC_Debug.list_all_toggles () in
  let uu___1 = FStarC_List.sortWith FStarC_String.compare keys in
  FStarC_List.iter
    (fun s -> FStarC_Format.print_string (FStarC_String.op_Hat s "\n"))
    uu___1
let usage_for (o : (FStarC_Getopt.opt * FStar_Pprint.document)) :
  FStar_Pprint.document=
  let uu___ = o in
  match uu___ with
  | ((short, flag, p), explain) ->
      let arg =
        match p with
        | FStarC_Getopt.ZeroArgs uu___1 -> FStar_Pprint.empty
        | FStarC_Getopt.OneArg (uu___1, argname) ->
            FStar_Pprint.op_Hat_Hat (FStar_Pprint.blank Prims.int_one)
              (FStar_Pprint.doc_of_string argname) in
      let short_opt =
        if short <> FStarC_Getopt.noshort
        then
          let uu___1 =
            let uu___2 =
              let uu___3 =
                let uu___4 = FStarC_String.make Prims.int_one short in
                FStarC_String.op_Hat "-" uu___4 in
              FStar_Pprint.doc_of_string uu___3 in
            FStar_Pprint.op_Hat_Hat uu___2 arg in
          [uu___1]
        else [] in
      let long_opt =
        if flag <> ""
        then
          [FStar_Pprint.op_Hat_Hat
             (FStar_Pprint.doc_of_string (FStarC_String.op_Hat "--" flag))
             arg]
        else [] in
      let uu___1 =
        let uu___2 =
          bold_doc
            (FStar_Pprint.separate
               (FStar_Pprint.op_Hat_Hat FStar_Pprint.comma
                  (FStar_Pprint.blank Prims.int_one))
               (FStarC_List.op_At short_opt long_opt)) in
        FStar_Pprint.group uu___2 in
      FStar_Pprint.op_Hat_Hat uu___1
        (FStar_Pprint.op_Hat_Hat FStar_Pprint.hardline
           (FStar_Pprint.op_Hat_Hat
              (FStar_Pprint.group
                 (FStar_Pprint.op_Hat_Hat
                    (FStar_Pprint.blank (Prims.of_int (4)))
                    (FStar_Pprint.align explain))) FStar_Pprint.hardline))
let display_usage_aux
  (specs : (FStarC_Getopt.opt * FStar_Pprint.document) Prims.list) : 
  unit=
  let text s =
    FStar_Pprint.flow (FStar_Pprint.break_ Prims.int_one)
      (FStar_Pprint.words s) in
  let d =
    let uu___ =
      let uu___1 =
        FStarC_List.fold_right
          (fun o rest ->
             let uu___2 = usage_for o in FStar_Pprint.op_Hat_Hat uu___2 rest)
          specs FStar_Pprint.empty in
      FStar_Pprint.op_Hat_Slash_Hat
        (FStar_Pprint.doc_of_string
           (FStarC_Format.fmt1
              "  %srespfile: read command-line options from respfile\n"
              (FStarC_Format.colorize_bold "@"))) uu___1 in
    FStar_Pprint.op_Hat_Slash_Hat
      (FStar_Pprint.doc_of_string
         "fstar.exe [options] file[s] [@respfile...]") uu___ in
  FStarC_Format.print_string
    (FStarC_Pprint.pretty_string (FStarC_Util.float_of_string "1.0")
       (Prims.of_int (80)) d)
let mk_spec
  (o :
    (FStarC_BaseTypes.char * Prims.string * option_val
      FStarC_Getopt.opt_variant))
  : FStarC_Getopt.opt=
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
let accumulated_option (name : Prims.string) (value : option_val) :
  option_val=
  let prev_values =
    let uu___ = lookup_opt name (as_option as_list') in
    FStarC_Option.dflt [] uu___ in
  List (value :: prev_values)
let reverse_accumulated_option (name : Prims.string) (value : option_val) :
  option_val=
  let prev_values =
    let uu___ = lookup_opt name (as_option as_list') in
    FStarC_Option.dflt [] uu___ in
  List (FStarC_List.op_At prev_values [value])
let accumulate_string (name : Prims.string)
  (post_processor : 'uuuuu -> Prims.string) (value : 'uuuuu) : unit=
  let uu___ = accumulated_option name (String (post_processor value)) in
  set_option name uu___
let add_extract_module (s : Prims.string) : unit=
  accumulate_string "extract_module" FStarC_String.lowercase s
let add_extract_namespace (s : Prims.string) : unit=
  accumulate_string "extract_namespace" FStarC_String.lowercase s
let add_verify_module (s : Prims.string) : unit=
  accumulate_string "verify_module" FStarC_String.lowercase s
exception InvalidArgument of Prims.string 
let uu___is_InvalidArgument (projectee : Prims.exn) : Prims.bool=
  match projectee with | InvalidArgument uu___ -> true | uu___ -> false
let __proj__InvalidArgument__item__uu___ (projectee : Prims.exn) :
  Prims.string= match projectee with | InvalidArgument uu___ -> uu___
let rec parse_opt_val (opt_name : Prims.string) (typ : opt_type)
  (str_val : Prims.string) : option_val=
  try
    (fun uu___ ->
       match () with
       | () ->
           (match typ with
            | Const c -> c
            | IntStr uu___1 ->
                (match FStarC_Util.safe_int_of_string str_val with
                 | FStar_Pervasives_Native.Some v -> Int v
                 | FStar_Pervasives_Native.None ->
                     FStarC_Effect.raise (InvalidArgument opt_name))
            | BoolStr ->
                let uu___1 =
                  if str_val = "true"
                  then true
                  else
                    if str_val = "false"
                    then false
                    else FStarC_Effect.raise (InvalidArgument opt_name) in
                Bool uu___1
            | PathStr uu___1 -> Path str_val
            | SimpleStr uu___1 -> String str_val
            | EnumStr strs ->
                if FStarC_List.mem str_val strs
                then String str_val
                else FStarC_Effect.raise (InvalidArgument opt_name)
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
                (side_effect (); parse_opt_val opt_name elem_spec str_val)))
      ()
  with
  | InvalidArgument opt_name1 ->
      FStarC_Effect.failwith
        (FStarC_Format.fmt1 "Invalid argument to --%s" opt_name1)
let rec desc_of_opt_type (typ : opt_type) :
  Prims.string FStar_Pervasives_Native.option=
  let desc_of_enum cases =
    FStar_Pervasives_Native.Some (FStarC_String.concat "|" cases) in
  match typ with
  | Const c -> FStar_Pervasives_Native.None
  | IntStr desc -> FStar_Pervasives_Native.Some desc
  | BoolStr -> desc_of_enum ["true"; "false"]
  | PathStr desc -> FStar_Pervasives_Native.Some desc
  | SimpleStr desc -> FStar_Pervasives_Native.Some desc
  | EnumStr strs -> desc_of_enum strs
  | OpenEnumStr (strs, desc) -> desc_of_enum (FStarC_List.op_At strs [desc])
  | PostProcessed (uu___, elem_spec) -> desc_of_opt_type elem_spec
  | Accumulated elem_spec -> desc_of_opt_type elem_spec
  | ReverseAccumulated elem_spec -> desc_of_opt_type elem_spec
  | WithSideEffect (uu___, elem_spec) -> desc_of_opt_type elem_spec
let arg_spec_of_opt_type (opt_name : Prims.string) (typ : opt_type) :
  option_val FStarC_Getopt.opt_variant=
  let wrap s = FStarC_String.op_Hat "<" (FStarC_String.op_Hat s ">") in
  let parser = parse_opt_val opt_name typ in
  match desc_of_opt_type typ with
  | FStar_Pervasives_Native.None ->
      FStarC_Getopt.ZeroArgs ((fun uu___ -> parser ""))
  | FStar_Pervasives_Native.Some desc ->
      let desc1 = wrap desc in FStarC_Getopt.OneArg (parser, desc1)
let pp_validate_dir (p : option_val) : option_val=
  let pp = as_string p in FStarC_Util.mkdir false true pp; p
let pp_lowercase (s : option_val) : option_val=
  let uu___ = let uu___1 = as_string s in FStarC_String.lowercase uu___1 in
  String uu___
let abort_counter : Prims.int FStarC_Effect.ref=
  FStarC_Effect.mk_ref Prims.int_zero
let interp_quake_arg (s : Prims.string) :
  (Prims.int * Prims.int * Prims.bool)=
  let ios = FStarC_Util.int_of_string in
  match FStarC_Util.split s "/" with
  | f::[] ->
      let uu___ = ios f in let uu___1 = ios f in (uu___, uu___1, false)
  | f1::f2::[] ->
      if f2 = "k"
      then let uu___ = ios f1 in let uu___1 = ios f1 in (uu___, uu___1, true)
      else
        (let uu___1 = ios f1 in
         let uu___2 = ios f2 in (uu___1, uu___2, false))
  | f1::f2::k::[] ->
      if k = "k"
      then let uu___ = ios f1 in let uu___1 = ios f2 in (uu___, uu___1, true)
      else FStarC_Effect.failwith "unexpected value for --quake"
  | uu___ -> FStarC_Effect.failwith "unexpected value for --quake"
let uu___1 : (((Prims.string -> unit) -> unit) * (Prims.string -> unit))=
  let cb = FStarC_Effect.mk_ref FStar_Pervasives_Native.None in
  let set1 f =
    FStarC_Effect.op_Colon_Equals cb (FStar_Pervasives_Native.Some f) in
  let call msg =
    let uu___ = FStarC_Effect.op_Bang cb in
    match uu___ with
    | FStar_Pervasives_Native.None -> ()
    | FStar_Pervasives_Native.Some f -> f msg in
  (set1, call)
let set_option_warning_callback_aux : (Prims.string -> unit) -> unit=
  match uu___1 with
  | (set_option_warning_callback_aux1, option_warning_callback) ->
      set_option_warning_callback_aux1
let option_warning_callback : Prims.string -> unit=
  match uu___1 with
  | (set_option_warning_callback_aux1, option_warning_callback1) ->
      option_warning_callback1
let set_option_warning_callback (f : Prims.string -> unit) : unit=
  set_option_warning_callback_aux f
let specs_with_types (warn_unsafe : Prims.bool) :
  (FStarC_BaseTypes.char * Prims.string * opt_type * FStar_Pprint.document)
    Prims.list=
  let text s =
    FStar_Pprint.flow (FStar_Pprint.break_ Prims.int_one)
      (FStar_Pprint.words s) in
  let uu___ =
    let uu___2 =
      let uu___3 =
        let uu___4 =
          let uu___5 =
            let uu___6 =
              let uu___7 =
                let uu___8 =
                  let uu___9 =
                    let uu___10 =
                      let uu___11 =
                        let uu___12 =
                          let uu___13 =
                            let uu___14 =
                              let uu___15 =
                                let uu___16 =
                                  let uu___17 =
                                    let uu___18 =
                                      let uu___19 =
                                        let uu___20 =
                                          let uu___21 =
                                            let uu___22 =
                                              FStarC_Errors_Msg.bulleted
                                                [text
                                                   "if 'no', no checks are performed";
                                                text
                                                  "if 'warn', checks are performed and raise a warning when they fail";
                                                text
                                                  "if 'error, like 'warn', but the compiler raises a hard error instead";
                                                text
                                                  "if 'abort, like 'warn', but the compiler immediately aborts on an error"] in
                                            FStar_Pprint.op_Hat_Slash_Hat
                                              uu___22 (text "(default 'no')") in
                                          FStar_Pprint.op_Hat_Hat
                                            (text
                                               "Enable several internal sanity checks, useful to track bugs and report issues.")
                                            uu___21 in
                                        (FStarC_Getopt.noshort, "defensive",
                                          (EnumStr
                                             ["no"; "warn"; "error"; "abort"]),
                                          uu___20) in
                                      let uu___20 =
                                        let uu___21 =
                                          let uu___22 =
                                            let uu___23 =
                                              FStarC_Errors_Msg.bulleted
                                                [text
                                                   "'graph': a format suitable the 'dot' tool from 'GraphViz'";
                                                text
                                                  "'full': a format suitable for 'make', including dependences for producing .ml and .krml files";
                                                text
                                                  "'make': (deprecated) a format suitable for 'make', including only dependences among source files"] in
                                            FStar_Pprint.op_Hat_Hat
                                              (text
                                                 "Output the transitive closure of the full dependency graph in three formats:")
                                              uu___23 in
                                          (FStarC_Getopt.noshort, "dep",
                                            (EnumStr
                                               ["make";
                                               "graph";
                                               "full";
                                               "raw"]), uu___22) in
                                        let uu___22 =
                                          let uu___23 =
                                            let uu___24 =
                                              let uu___25 =
                                                let uu___26 =
                                                  let uu___27 =
                                                    let uu___28 =
                                                      let uu___29 =
                                                        let uu___30 =
                                                          let uu___31 =
                                                            let uu___32 =
                                                              let uu___33 =
                                                                let uu___34 =
                                                                  let uu___35
                                                                    =
                                                                    let uu___36
                                                                    =
                                                                    let uu___37
                                                                    =
                                                                    let uu___38
                                                                    =
                                                                    let uu___39
                                                                    =
                                                                    let uu___40
                                                                    =
                                                                    let uu___41
                                                                    =
                                                                    let uu___42
                                                                    =
                                                                    let uu___43
                                                                    =
                                                                    let uu___44
                                                                    =
                                                                    let uu___45
                                                                    =
                                                                    let uu___46
                                                                    =
                                                                    let uu___47
                                                                    =
                                                                    let uu___48
                                                                    =
                                                                    let uu___49
                                                                    =
                                                                    let uu___50
                                                                    =
                                                                    let uu___51
                                                                    =
                                                                    let uu___52
                                                                    =
                                                                    let uu___53
                                                                    =
                                                                    let uu___54
                                                                    =
                                                                    let uu___55
                                                                    =
                                                                    let uu___56
                                                                    =
                                                                    let uu___57
                                                                    =
                                                                    let uu___58
                                                                    =
                                                                    let uu___59
                                                                    =
                                                                    let uu___60
                                                                    =
                                                                    let uu___61
                                                                    =
                                                                    let uu___62
                                                                    =
                                                                    let uu___63
                                                                    =
                                                                    let uu___64
                                                                    =
                                                                    let uu___65
                                                                    =
                                                                    let uu___66
                                                                    =
                                                                    let uu___67
                                                                    =
                                                                    let uu___68
                                                                    =
                                                                    let uu___69
                                                                    =
                                                                    let uu___70
                                                                    =
                                                                    let uu___71
                                                                    =
                                                                    let uu___72
                                                                    =
                                                                    let uu___73
                                                                    =
                                                                    let uu___74
                                                                    =
                                                                    let uu___75
                                                                    =
                                                                    let uu___76
                                                                    =
                                                                    let uu___77
                                                                    =
                                                                    let uu___78
                                                                    =
                                                                    let uu___79
                                                                    =
                                                                    let uu___80
                                                                    =
                                                                    let uu___81
                                                                    =
                                                                    let uu___82
                                                                    =
                                                                    FStarC_Errors_Msg.bulleted
                                                                    [
                                                                    text
                                                                    "--quake N/M repeats each query checks that it succeeds at least N out of M times, aborting early if possible";
                                                                    text
                                                                    "--quake N/M/k works as above, except it will unconditionally run M times";
                                                                    text
                                                                    "--quake N is an alias for --quake N/N";
                                                                    text
                                                                    "--quake N/k is an alias for --quake N/N/k"] in
                                                                    FStar_Pprint.op_Hat_Hat
                                                                    uu___82
                                                                    (text
                                                                    "Using --quake disables --retry. When quake testing, queries are not splitted for error reporting unless '--split_queries always' is given. Queries from the smt_sync tactic are not quake-tested.") in
                                                                    FStar_Pprint.op_Hat_Hat
                                                                    (text
                                                                    "Repeats SMT queries to check for robustness")
                                                                    uu___81 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "quake",
                                                                    (PostProcessed
                                                                    ((fun
                                                                    uu___81
                                                                    ->
                                                                    match uu___81
                                                                    with
                                                                    | 
                                                                    String s
                                                                    ->
                                                                    let uu___82
                                                                    =
                                                                    interp_quake_arg
                                                                    s in
                                                                    (match uu___82
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
                                                                    uu___82
                                                                    ->
                                                                    FStarC_Effect.failwith
                                                                    "impos"),
                                                                    (SimpleStr
                                                                    "positive integer or pair of positive integers"))),
                                                                    uu___80) in
                                                                    let uu___80
                                                                    =
                                                                    let uu___81
                                                                    =
                                                                    let uu___82
                                                                    =
                                                                    let uu___83
                                                                    =
                                                                    let uu___84
                                                                    =
                                                                    let uu___85
                                                                    =
                                                                    let uu___86
                                                                    =
                                                                    let uu___87
                                                                    =
                                                                    let uu___88
                                                                    =
                                                                    let uu___89
                                                                    =
                                                                    let uu___90
                                                                    =
                                                                    let uu___91
                                                                    =
                                                                    let uu___92
                                                                    =
                                                                    let uu___93
                                                                    =
                                                                    let uu___94
                                                                    =
                                                                    let uu___95
                                                                    =
                                                                    let uu___96
                                                                    =
                                                                    FStarC_Errors_Msg.bulleted
                                                                    [
                                                                    text
                                                                    "if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'";
                                                                    text
                                                                    "if 'native' use '*, div, mod'";
                                                                    text
                                                                    "if 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'"] in
                                                                    FStar_Pprint.op_Hat_Hat
                                                                    uu___96
                                                                    (text
                                                                    "(default 'boxwrap')") in
                                                                    FStar_Pprint.op_Hat_Hat
                                                                    (text
                                                                    "Control the representation of non-linear arithmetic functions in the SMT encoding:")
                                                                    uu___95 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "smtencoding.nl_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "wrapped";
                                                                    "boxwrap"]),
                                                                    uu___94) in
                                                                    let uu___94
                                                                    =
                                                                    let uu___95
                                                                    =
                                                                    let uu___96
                                                                    =
                                                                    let uu___97
                                                                    =
                                                                    let uu___98
                                                                    =
                                                                    FStarC_Errors_Msg.bulleted
                                                                    [
                                                                    text
                                                                    "if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'";
                                                                    text
                                                                    "if 'native', use '+, -, -'"] in
                                                                    FStar_Pprint.op_Hat_Hat
                                                                    uu___98
                                                                    (text
                                                                    "(default 'boxwrap')") in
                                                                    FStar_Pprint.op_Hat_Hat
                                                                    (text
                                                                    "Toggle the representation of linear arithmetic functions in the SMT encoding:")
                                                                    uu___97 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "smtencoding.l_arith_repr",
                                                                    (EnumStr
                                                                    ["native";
                                                                    "boxwrap"]),
                                                                    uu___96) in
                                                                    let uu___96
                                                                    =
                                                                    let uu___97
                                                                    =
                                                                    let uu___98
                                                                    =
                                                                    let uu___99
                                                                    =
                                                                    let uu___100
                                                                    =
                                                                    let uu___101
                                                                    =
                                                                    FStarC_Errors_Msg.bulleted
                                                                    [
                                                                    text
                                                                    "Use 'no' to disable (this may reduce the quality of error messages).";
                                                                    text
                                                                    "Use 'on_failure' to split queries and retry when discharging fails (the default)";
                                                                    text
                                                                    "Use 'yes' to always split."] in
                                                                    FStar_Pprint.op_Hat_Hat
                                                                    (text
                                                                    "Split SMT verification conditions into several separate queries, one per goal. Helps with localizing errors.")
                                                                    uu___101 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "split_queries",
                                                                    (EnumStr
                                                                    ["no";
                                                                    "on_failure";
                                                                    "always"]),
                                                                    uu___100) in
                                                                    let uu___100
                                                                    =
                                                                    let uu___101
                                                                    =
                                                                    let uu___102
                                                                    =
                                                                    let uu___103
                                                                    =
                                                                    let uu___104
                                                                    =
                                                                    let uu___105
                                                                    =
                                                                    let uu___106
                                                                    =
                                                                    let uu___107
                                                                    =
                                                                    let uu___108
                                                                    =
                                                                    let uu___109
                                                                    =
                                                                    let uu___110
                                                                    =
                                                                    let uu___111
                                                                    =
                                                                    let uu___112
                                                                    =
                                                                    let uu___113
                                                                    =
                                                                    let uu___114
                                                                    =
                                                                    let uu___115
                                                                    =
                                                                    let uu___116
                                                                    =
                                                                    let uu___117
                                                                    =
                                                                    let uu___118
                                                                    =
                                                                    let uu___119
                                                                    =
                                                                    let uu___120
                                                                    =
                                                                    let uu___121
                                                                    =
                                                                    let uu___122
                                                                    =
                                                                    let uu___123
                                                                    =
                                                                    let uu___124
                                                                    =
                                                                    let uu___125
                                                                    =
                                                                    let uu___126
                                                                    =
                                                                    let uu___127
                                                                    =
                                                                    let uu___128
                                                                    =
                                                                    let uu___129
                                                                    =
                                                                    let uu___130
                                                                    =
                                                                    let uu___131
                                                                    =
                                                                    let uu___132
                                                                    =
                                                                    let uu___133
                                                                    =
                                                                    let uu___134
                                                                    =
                                                                    FStarC_Errors_Msg.bulleted
                                                                    [
                                                                    text
                                                                    "[r] is a range of warnings (either a number [n], or a range [n..n])";
                                                                    text
                                                                    "[-r] silences range [r]";
                                                                    text
                                                                    "[+r] enables range [r] as warnings (NOTE: \"enabling\" an error will downgrade it to a warning)";
                                                                    text
                                                                    "[@r] makes range [r] fatal."] in
                                                                    FStar_Pprint.op_Hat_Hat
                                                                    (text
                                                                    "The [-warn_error] option follows the OCaml syntax, namely:")
                                                                    uu___134 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "warn_error",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "")),
                                                                    uu___133) in
                                                                    [uu___132;
                                                                    (FStarC_Getopt.noshort,
                                                                    "use_nbe",
                                                                    BoolStr,
                                                                    (text
                                                                    "Use normalization by evaluation as the default normalization strategy (default 'false')"));
                                                                    (FStarC_Getopt.noshort,
                                                                    "use_nbe_for_extraction",
                                                                    BoolStr,
                                                                    (text
                                                                    "Use normalization by evaluation for normalizing terms before extraction (default 'false')"));
                                                                    (FStarC_Getopt.noshort,
                                                                    "trivial_pre_for_unannotated_effectful_fns",
                                                                    BoolStr,
                                                                    (text
                                                                    "Enforce trivial preconditions for unannotated effectful functions (default 'true')"));
                                                                    (FStarC_Getopt.noshort,
                                                                    "with_fstarc",
                                                                    (WithSideEffect
                                                                    (((
                                                                    fun
                                                                    uu___133
                                                                    ->
                                                                    FStarC_Find.set_with_fstarc
                                                                    true)),
                                                                    (Const
                                                                    (Bool
                                                                    true)))),
                                                                    (text
                                                                    "Expose compiler internal modules (FStarC namespace). Only for advanced plugins you should probably not use it."));
                                                                    (FStarC_Getopt.noshort,
                                                                    "__debug_embedding",
                                                                    (WithSideEffect
                                                                    (((
                                                                    fun
                                                                    uu___133
                                                                    ->
                                                                    FStarC_Effect.op_Colon_Equals
                                                                    debug_embedding
                                                                    true)),
                                                                    (Const
                                                                    (Bool
                                                                    true)))),
                                                                    (text
                                                                    "Debug messages for embeddings/unembeddings of natively compiled terms"));
                                                                    (FStarC_Getopt.noshort,
                                                                    "eager_embedding",
                                                                    (WithSideEffect
                                                                    (((
                                                                    fun
                                                                    uu___133
                                                                    ->
                                                                    FStarC_Effect.op_Colon_Equals
                                                                    eager_embedding
                                                                    true)),
                                                                    (Const
                                                                    (Bool
                                                                    true)))),
                                                                    (text
                                                                    "Eagerly embed and unembed terms to primitive operations and plugins: not recommended except for benchmarking"));
                                                                    (FStarC_Getopt.noshort,
                                                                    "profile_group_by_decl",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    (text
                                                                    "Emit profiles grouped by declaration rather than by module"));
                                                                    (FStarC_Getopt.noshort,
                                                                    "profile_component",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | module | identifier)'")),
                                                                    (text
                                                                    "Specific source locations in the compiler are instrumented with profiling counters. Pass `--profile_component FStarC.TypeChecker` to enable all counters in the FStarC.TypeChecker namespace. This option is a module or namespace selector, like many other options (e.g., `--extract`)"));
                                                                    (FStarC_Getopt.noshort,
                                                                    "profile",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
                                                                    (text
                                                                    "Profiling can be enabled when the compiler is processing a given set of source modules. Pass `--profile FStar.Pervasives` to enable profiling when the compiler is processing any module in FStar.Pervasives. This option is a module or namespace selector, like many other options (e.g., `--extract`)"));
                                                                    (104,
                                                                    "help",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    (text
                                                                    "Display this information"));
                                                                    (FStarC_Getopt.noshort,
                                                                    "list_debug_keys",
                                                                    (WithSideEffect
                                                                    (((
                                                                    fun
                                                                    uu___133
                                                                    ->
                                                                    display_debug_keys
                                                                    ();
                                                                    FStarC_Effect.exit
                                                                    Prims.int_zero)),
                                                                    (Const
                                                                    (Bool
                                                                    true)))),
                                                                    (text
                                                                    "List all debug keys and exit"));
                                                                    (FStarC_Getopt.noshort,
                                                                    "expand_include",
                                                                    (SimpleStr
                                                                    "directory"),
                                                                    (text
                                                                    "Print all directories that would be transitively included (due to fstar.include files) by including the given directory."));
                                                                    (FStarC_Getopt.noshort,
                                                                    "list_plugins",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    (text
                                                                    "List all registered plugins and exit"));
                                                                    (FStarC_Getopt.noshort,
                                                                    "locate",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    (text
                                                                    "Print the root of the F* installation and exit"));
                                                                    (FStarC_Getopt.noshort,
                                                                    "locate_lib",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    (text
                                                                    "Print the root of the F* library and exit"));
                                                                    (FStarC_Getopt.noshort,
                                                                    "locate_ocaml",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    (text
                                                                    "Print the root of the built OCaml F* library and exit"));
                                                                    (FStarC_Getopt.noshort,
                                                                    "locate_file",
                                                                    (SimpleStr
                                                                    "basename"),
                                                                    (text
                                                                    "Find a file in F*'s include path and print its absolute path, then exit"));
                                                                    (FStarC_Getopt.noshort,
                                                                    "locate_z3",
                                                                    (SimpleStr
                                                                    "version"),
                                                                    (text
                                                                    "Locate the executable for a given Z3 version, then exit. The output is either an absolute path, or a name that was found in the PATH. Note: this is the Z3 executable that F* will attempt to call for the given version, but the version check is not performed at this point."));
                                                                    (FStarC_Getopt.noshort,
                                                                    "ocamlenv",
                                                                    (WithSideEffect
                                                                    (((
                                                                    fun
                                                                    uu___133
                                                                    ->
                                                                    FStarC_Format.print_error
                                                                    "--ocamlenv must be the first argument, see fstar.exe --help for details\n";
                                                                    FStarC_Effect.exit
                                                                    Prims.int_one)),
                                                                    (Const
                                                                    (Bool
                                                                    true)))),
                                                                    (text
                                                                    "With no arguments: print shell code to set up an environment with the OCaml libraries in scope (similar to 'opam env'). With arguments: run a command in that environment. NOTE: this must be the FIRST argument passed to F* and other options are NOT processed."));
                                                                    (FStarC_Getopt.noshort,
                                                                    "ocamlc",
                                                                    (WithSideEffect
                                                                    (((
                                                                    fun
                                                                    uu___133
                                                                    ->
                                                                    FStarC_Format.print_error
                                                                    "--ocamlc must be the first argument, see fstar.exe --help for details\n";
                                                                    FStarC_Effect.exit
                                                                    Prims.int_one)),
                                                                    (Const
                                                                    (Bool
                                                                    true)))),
                                                                    (text
                                                                    "A helper. This runs 'ocamlc' in the environment set up by --ocamlenv, for building an F* application bytecode executable."));
                                                                    (FStarC_Getopt.noshort,
                                                                    "ocamlopt",
                                                                    (WithSideEffect
                                                                    (((
                                                                    fun
                                                                    uu___133
                                                                    ->
                                                                    FStarC_Format.print_error
                                                                    "--ocamlopt must be the first argument, see fstar.exe --help for details\n";
                                                                    FStarC_Effect.exit
                                                                    Prims.int_one)),
                                                                    (Const
                                                                    (Bool
                                                                    true)))),
                                                                    (text
                                                                    "A helper. This runs 'ocamlopt' in the environment set up by --ocamlenv, for building an F* application native executable."));
                                                                    (FStarC_Getopt.noshort,
                                                                    "ocamlopt_plugin",
                                                                    (WithSideEffect
                                                                    (((
                                                                    fun
                                                                    uu___133
                                                                    ->
                                                                    FStarC_Format.print_error
                                                                    "--ocamlopt_plugin must be the first argument, see fstar.exe --help for details\n";
                                                                    FStarC_Effect.exit
                                                                    Prims.int_one)),
                                                                    (Const
                                                                    (Bool
                                                                    true)))),
                                                                    (text
                                                                    "A helper. This runs 'ocamlopt' in the environment set up by --ocamlenv, for building an F* plugin."))] in
                                                                    (FStarC_Getopt.noshort,
                                                                    "__no_positivity",
                                                                    (WithSideEffect
                                                                    ((fun
                                                                    uu___132
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
                                                                    (text
                                                                    "Don't check positivity of inductive types"))
                                                                    ::
                                                                    uu___131 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "z3version",
                                                                    (SimpleStr
                                                                    "version"),
                                                                    (text
                                                                    "Set the version of Z3 that is to be used. Default: 4.13.3"))
                                                                    ::
                                                                    uu___130 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "z3seed",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    (text
                                                                    "Set the Z3 random seed (default 0)"))
                                                                    ::
                                                                    uu___129 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "z3rlimit_factor",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    (text
                                                                    "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)"))
                                                                    ::
                                                                    uu___128 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "z3rlimit",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    (text
                                                                    "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)"))
                                                                    ::
                                                                    uu___127 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "z3refresh",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    (text
                                                                    "Restart Z3 after each query; useful for ensuring proof robustness"))
                                                                    ::
                                                                    uu___126 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "z3smtopt",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "option")),
                                                                    (text
                                                                    "Z3 options in smt2 format"))
                                                                    ::
                                                                    uu___125 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "z3cliopt",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "option")),
                                                                    (text
                                                                    "Z3 command line options"))
                                                                    ::
                                                                    uu___124 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "warn_default_effects",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    (text
                                                                    "Warn when (a -> b) is desugared to (a -> Tot b)"))
                                                                    ::
                                                                    uu___123 in
                                                                    (118,
                                                                    "version",
                                                                    (WithSideEffect
                                                                    ((fun
                                                                    uu___123
                                                                    ->
                                                                    display_version
                                                                    ();
                                                                    FStarC_Effect.exit
                                                                    Prims.int_zero),
                                                                    (Const
                                                                    (Bool
                                                                    true)))),
                                                                    (text
                                                                    "Display version number"))
                                                                    ::
                                                                    uu___122 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "__temp_fast_implicits",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    (text
                                                                    "This does nothing and will be removed"))
                                                                    ::
                                                                    uu___121 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "using_facts_from",
                                                                    (ReverseAccumulated
                                                                    (SimpleStr
                                                                    "One or more space-separated occurrences of '[+|-]( * | namespace | fact id)'")),
                                                                    (text
                                                                    "Prunes the context to include only the facts from the given namespace or fact id. Facts can be include or excluded using the [+|-] qualifier. For example --using_facts_from '* -FStarC.Reflection +FStarC.List -FStarC.List.Tot' will remove all facts from FStarC.List.Tot.*, retain all remaining facts from FStarC.List.*, remove all facts from FStarC.Reflection.*, and retain all the rest. Note, the '+' is optional: --using_facts_from 'FStarC.List' is equivalent to --using_facts_from '+FStarC.List'. Multiple uses of this option accumulate, e.g., --using_facts_from A --using_facts_from B is interpreted as --using_facts_from A^B."))
                                                                    ::
                                                                    uu___120 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "no_tactics",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    (text
                                                                    "Do not run the tactic engine before discharging a VC"))
                                                                    ::
                                                                    uu___119 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "no_plugins",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    (text
                                                                    "Do not run plugins natively and interpret them as usual instead"))
                                                                    ::
                                                                    uu___118 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "use_native_tactics",
                                                                    (PathStr
                                                                    "path"),
                                                                    (text
                                                                    "Use compiled tactics from  path"))
                                                                    ::
                                                                    uu___117 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "use_hint_hashes",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    (text
                                                                    "Admit queries if their hash matches the hash recorded in the hints database"))
                                                                    ::
                                                                    uu___116 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "use_hints",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    (text
                                                                    "Use a previously recorded hints database for proof replay"))
                                                                    ::
                                                                    uu___115 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "use_eq_at_higher_order",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    (text
                                                                    "Use equality constraints when comparing higher-order types (Temporary)"))
                                                                    ::
                                                                    uu___114 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "unsafe_tactic_exec",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    (text
                                                                    "Allow tactics to run external processes. WARNING: checking an untrusted F* file while using this option can have disastrous effects."))
                                                                    ::
                                                                    uu___113 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "unthrottle_inductives",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    (text
                                                                    "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)"))
                                                                    ::
                                                                    uu___112 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "ugly",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    (text
                                                                    "Emit output formatted for debugging"))
                                                                    ::
                                                                    uu___111 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "trace_error",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    (text
                                                                    "Attach stack traces on errors"))
                                                                    ::
                                                                    uu___110 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "timing",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    (text
                                                                    "Print the time it takes to verify each top-level definition. This is just an alias for an invocation of the profiler, so it may not work well if combined with --profile. In particular, it implies --profile_group_by_decl."))
                                                                    ::
                                                                    uu___109 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "tcnorm",
                                                                    BoolStr,
                                                                    (text
                                                                    "Attempt to normalize definitions marked as tcnorm (default 'true')"))
                                                                    ::
                                                                    uu___108 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "__tactics_nbe",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    (text
                                                                    "Use NBE to evaluate metaprograms (experimental)"))
                                                                    ::
                                                                    uu___107 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "tactic_trace_d",
                                                                    (IntStr
                                                                    "positive_integer"),
                                                                    (text
                                                                    "Trace tactics up to a certain binding depth"))
                                                                    ::
                                                                    uu___106 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "tactic_trace",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    (text
                                                                    "Print a depth-indexed trace of tactic execution (Warning: very verbose)"))
                                                                    ::
                                                                    uu___105 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "tactics_info",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    (text
                                                                    "Print some rough information on tactics, such as the time they take to run"))
                                                                    ::
                                                                    uu___104 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "tactics_failhard",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    (text
                                                                    "Do not recover from metaprogramming errors, and abort if one occurs"))
                                                                    ::
                                                                    uu___103 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "tactic_raw_binders",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    (text
                                                                    "Do not use the lexical scope of tactics to improve binder names"))
                                                                    ::
                                                                    uu___102 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "stats",
                                                                    (PostProcessed
                                                                    ((fun b
                                                                    ->
                                                                    (
                                                                    match b
                                                                    with
                                                                    | 
                                                                    Bool
                                                                    (true) ->
                                                                    (FStarC_Effect.op_Colon_Equals
                                                                    FStarC_Stats.enabled
                                                                    true;
                                                                    FStarC_Effect.op_Colon_Equals
                                                                    FStarC_Stats.ever_enabled
                                                                    true)
                                                                    | 
                                                                    Bool
                                                                    (false)
                                                                    ->
                                                                    FStarC_Effect.op_Colon_Equals
                                                                    FStarC_Stats.enabled
                                                                    false
                                                                    | 
                                                                    uu___103
                                                                    -> ());
                                                                    b),
                                                                    BoolStr)),
                                                                    (text
                                                                    "Print some statistics on the time spent in each phase of the compiler"))
                                                                    ::
                                                                    uu___101 in
                                                                    uu___99
                                                                    ::
                                                                    uu___100 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "smtencoding.valid_elim",
                                                                    BoolStr,
                                                                    (text
                                                                    "Include an axiom in the SMT encoding to eliminate proof-irrelevance into the existence of a proof witness"))
                                                                    ::
                                                                    uu___98 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "smtencoding.valid_intro",
                                                                    BoolStr,
                                                                    (text
                                                                    "Include an axiom in the SMT encoding to introduce proof-irrelevance from a constructive proof"))
                                                                    ::
                                                                    uu___97 in
                                                                    uu___95
                                                                    ::
                                                                    uu___96 in
                                                                    uu___93
                                                                    ::
                                                                    uu___94 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "smtencoding.elim_box",
                                                                    BoolStr,
                                                                    (text
                                                                    "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')"))
                                                                    ::
                                                                    uu___92 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "smt",
                                                                    (PathStr
                                                                    "path"),
                                                                    (text
                                                                    "Path to the Z3 SMT solver (we could eventually support other solvers)"))
                                                                    ::
                                                                    uu___91 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "silent",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    (text
                                                                    "Disable all non-critical output"))
                                                                    ::
                                                                    uu___90 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "report_assumes",
                                                                    (EnumStr
                                                                    ["warn";
                                                                    "error"]),
                                                                    (text
                                                                    "Report every use of an escape hatch, include assume, admit, etc."))
                                                                    ::
                                                                    uu___89 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "reuse_hint_for",
                                                                    (SimpleStr
                                                                    "toplevel_name"),
                                                                    (text
                                                                    "Optimistically, attempt using the recorded hint for  toplevel_name (a top-level name in the current module) when trying to verify some other term 'g'"))
                                                                    ::
                                                                    uu___88 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "retry",
                                                                    (PostProcessed
                                                                    ((fun
                                                                    uu___88
                                                                    ->
                                                                    match uu___88
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
                                                                    uu___89
                                                                    ->
                                                                    FStarC_Effect.failwith
                                                                    "impos"),
                                                                    (IntStr
                                                                    "positive integer"))),
                                                                    (text
                                                                    "Retry each SMT query N times and succeed on the first try. Using --retry disables --quake."))
                                                                    ::
                                                                    uu___87 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "record_options",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    (text
                                                                    "Record the state of options used to check each sigelt, useful for the `check_with` attribute and metaprogramming. Note that this implies a performance hit and increases the size of checked files."))
                                                                    ::
                                                                    uu___86 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "record_hints",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    (text
                                                                    "Record a database of hints for efficient proof replay"))
                                                                    ::
                                                                    uu___85 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "read_krml_file",
                                                                    (PathStr
                                                                    "path"),
                                                                    (text
                                                                    "Read a Karamel binary file and dump it to standard output."))
                                                                    ::
                                                                    uu___84 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "read_checked_file",
                                                                    (PathStr
                                                                    "path"),
                                                                    (text
                                                                    "Read a checked file and dump it to standard output."))
                                                                    ::
                                                                    uu___83 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "query_stats",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    (text
                                                                    "Print SMT query statistics"))
                                                                    ::
                                                                    uu___82 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "query_cache",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    (text
                                                                    "Keep a running cache of SMT queries to make verification faster. Only available in the interactive mode. NOTE: This feature is experimental and potentially unsound! Hence why\n          it is not allowed in batch mode (where it is also less useful). If you\n          find a query that is mistakenly accepted with the cache, please\n          report a bug to the F* issue tracker on GitHub."))
                                                                    ::
                                                                    uu___81 in
                                                                    uu___79
                                                                    ::
                                                                    uu___80 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "proof_recovery",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    (text
                                                                    "Proof recovery mode: before failing an SMT query, retry 3 times, increasing rlimits. If the query goes through after retrying, verification will succeed, but a warning will be emitted. This feature is useful to restore a project after some change to its libraries or F* upgrade. Importantly, then, this option cannot be used in a pragma (#set-options, etc)."))
                                                                    ::
                                                                    uu___78 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "prn",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    (text
                                                                    "Print full names (deprecated; use --print_full_names instead)"))
                                                                    ::
                                                                    uu___77 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "print_z3_statistics",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    (text
                                                                    "Print Z3 statistics for each SMT query (details such as relevant modules, facts, etc. for each proof)"))
                                                                    ::
                                                                    uu___76 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "print_universes",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    (text
                                                                    "Print universes"))
                                                                    ::
                                                                    uu___75 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "print_implicits",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    (text
                                                                    "Print implicit arguments"))
                                                                    ::
                                                                    uu___74 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "print_full_names",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    (text
                                                                    "Print full names of variables"))
                                                                    ::
                                                                    uu___73 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "print_expected_failures",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    (text
                                                                    "Print the errors generated by declarations marked with expect_failure, useful for debugging error locations"))
                                                                    ::
                                                                    uu___72 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "print_effect_args",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    (text
                                                                    "Print inferred predicate transformers for all computation types"))
                                                                    ::
                                                                    uu___71 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "print_bound_var_types",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    (text
                                                                    "Print the types of bound variables"))
                                                                    ::
                                                                    uu___70 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "prims",
                                                                    (PathStr
                                                                    "file"),
                                                                    (text
                                                                    "Use a custom Prims.fst file. Do not use if you do not know exactly what you're doing."))
                                                                    ::
                                                                    uu___69 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "output_deps_to",
                                                                    (PathStr
                                                                    "file"),
                                                                    (text
                                                                    "[Deprecated: use -o instead.] Output the result of --dep into this file instead of to standard output."))
                                                                    ::
                                                                    uu___68 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "odir",
                                                                    (PostProcessed
                                                                    ((fun
                                                                    uu___68
                                                                    ->
                                                                    match uu___68
                                                                    with
                                                                    | 
                                                                    Path s ->
                                                                    (FStarC_Find.set_odir
                                                                    s;
                                                                    Unset)),
                                                                    (PathStr
                                                                    "dir"))),
                                                                    (text
                                                                    "Place output in directory  dir"))
                                                                    ::
                                                                    uu___67 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "krmloutput",
                                                                    (PathStr
                                                                    "filename"),
                                                                    (text
                                                                    "[Deprecated: use -o instead.] Place KaRaMeL extraction output in file <filename>. The path can be relative or absolute and does not dependon the --odir option."))
                                                                    ::
                                                                    uu___66 in
                                                                    (111,
                                                                    "output_to",
                                                                    (PathStr
                                                                    "filename"),
                                                                    (text
                                                                    "Write output (checked file, depend file, extracted output, etc) to this file."))
                                                                    ::
                                                                    uu___65 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "normalize_pure_terms_for_extraction",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    (text
                                                                    "Extract top-level pure terms after normalizing them. This can lead to very large code, but can result in more partial evaluation and compile-time specialization."))
                                                                    ::
                                                                    uu___64 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "no_smt",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    (text
                                                                    "Do not send any queries to the SMT solver, and fail on them instead"))
                                                                    ::
                                                                    uu___63 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "no_prelude",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    (text
                                                                    "Do not include the prelude module (FStar.Prelude) when checking the files given in the command line. This is similar to attaching [@@\"no_prelude\"] to the module."))
                                                                    ::
                                                                    uu___62 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "no_location_info",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    (text
                                                                    "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)"))
                                                                    ::
                                                                    uu___61 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "no_extract",
                                                                    (Accumulated
                                                                    (PathStr
                                                                    "module name")),
                                                                    (text
                                                                    "Deprecated: use --extract instead; Do not extract code from this module"))
                                                                    ::
                                                                    uu___60 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "no_default_includes",
                                                                    (WithSideEffect
                                                                    ((fun
                                                                    uu___60
                                                                    ->
                                                                    FStarC_Find.set_no_default_includes
                                                                    true),
                                                                    (Const
                                                                    (Bool
                                                                    true)))),
                                                                    (text
                                                                    "Ignore the default module search paths"))
                                                                    ::
                                                                    uu___59 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "max_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    (text
                                                                    "Number of unrolling of inductive datatypes to try at most (default 2)"))
                                                                    ::
                                                                    uu___58 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "max_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    (text
                                                                    "Number of unrolling of recursive functions to try at most (default 8)"))
                                                                    ::
                                                                    uu___57 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "log_failing_queries",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    (text
                                                                    "As --log_queries, but only save the failing queries. Each query is\n    saved in its own file regardless of whether they were checked during the\n    same invocation. The SMT2 file names begin with \"failedQueries\""))
                                                                    ::
                                                                    uu___56 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "log_queries",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    (text
                                                                    "Log the Z3 queries in several queries-*.smt2 files, as we go"))
                                                                    ::
                                                                    uu___55 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "log_types",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    (text
                                                                    "Print types computed for data/val/let-bindings"))
                                                                    ::
                                                                    uu___54 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "load_cmxs",
                                                                    (ReverseAccumulated
                                                                    (PathStr
                                                                    "module")),
                                                                    (text
                                                                    "Load compiled module, fails hard if the module is not already compiled"))
                                                                    ::
                                                                    uu___53 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "load",
                                                                    (ReverseAccumulated
                                                                    (PathStr
                                                                    "module")),
                                                                    (text
                                                                    "Load OCaml module, compiling it if necessary"))
                                                                    ::
                                                                    uu___52 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "lax",
                                                                    (WithSideEffect
                                                                    ((fun
                                                                    uu___52
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
                                                                    (text
                                                                    "Run the lax-type checker only (admit all verification conditions)"))
                                                                    ::
                                                                    uu___51 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "lang_extensions",
                                                                    (Accumulated
                                                                    (SimpleStr
                                                                    "extension")),
                                                                    (text
                                                                    "Automatically enable the given language extensions based on the file extension; the language extension's .cmxs must be on the include path or loaded with --load_cmxs"))
                                                                    ::
                                                                    uu___50 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "keep_query_captions",
                                                                    BoolStr,
                                                                    (text
                                                                    "Retain comments in the logged SMT queries (requires --log_queries or --log_failing_queries; default true)"))
                                                                    ::
                                                                    uu___49 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "initial_ifuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    (text
                                                                    "Number of unrolling of inductive datatypes to try at first (default 1)"))
                                                                    ::
                                                                    uu___48 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "initial_fuel",
                                                                    (IntStr
                                                                    "non-negative integer"),
                                                                    (text
                                                                    "Number of unrolling of recursive functions to try initially (default 2)"))
                                                                    ::
                                                                    uu___47 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "ifuel",
                                                                    (PostProcessed
                                                                    ((fun
                                                                    uu___47
                                                                    ->
                                                                    match uu___47
                                                                    with
                                                                    | 
                                                                    String s
                                                                    ->
                                                                    let p f =
                                                                    let uu___48
                                                                    =
                                                                    FStarC_Util.int_of_string
                                                                    f in
                                                                    Int
                                                                    uu___48 in
                                                                    let uu___48
                                                                    =
                                                                    match 
                                                                    FStarC_Util.split
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
                                                                    uu___49
                                                                    ->
                                                                    FStarC_Effect.failwith
                                                                    "unexpected value for --ifuel" in
                                                                    (match uu___48
                                                                    with
                                                                    | 
                                                                    (min,
                                                                    max) ->
                                                                    ((
                                                                    let uu___50
                                                                    = p min in
                                                                    set_option
                                                                    "initial_ifuel"
                                                                    uu___50);
                                                                    (let uu___51
                                                                    = p max in
                                                                    set_option
                                                                    "max_ifuel"
                                                                    uu___51);
                                                                    String s))
                                                                    | 
                                                                    uu___48
                                                                    ->
                                                                    FStarC_Effect.failwith
                                                                    "impos"),
                                                                    (SimpleStr
                                                                    "non-negative integer or pair of non-negative integers"))),
                                                                    (text
                                                                    "Set initial_ifuel and max_ifuel at once"))
                                                                    ::
                                                                    uu___46 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "fuel",
                                                                    (PostProcessed
                                                                    ((fun
                                                                    uu___46
                                                                    ->
                                                                    match uu___46
                                                                    with
                                                                    | 
                                                                    String s
                                                                    ->
                                                                    let p f =
                                                                    let uu___47
                                                                    =
                                                                    FStarC_Util.int_of_string
                                                                    f in
                                                                    Int
                                                                    uu___47 in
                                                                    let uu___47
                                                                    =
                                                                    match 
                                                                    FStarC_Util.split
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
                                                                    uu___48
                                                                    ->
                                                                    FStarC_Effect.failwith
                                                                    "unexpected value for --fuel" in
                                                                    (match uu___47
                                                                    with
                                                                    | 
                                                                    (min,
                                                                    max) ->
                                                                    ((
                                                                    let uu___49
                                                                    = p min in
                                                                    set_option
                                                                    "initial_fuel"
                                                                    uu___49);
                                                                    (let uu___50
                                                                    = p max in
                                                                    set_option
                                                                    "max_fuel"
                                                                    uu___50);
                                                                    String s))
                                                                    | 
                                                                    uu___47
                                                                    ->
                                                                    FStarC_Effect.failwith
                                                                    "impos"),
                                                                    (SimpleStr
                                                                    "non-negative integer or pair of non-negative integers"))),
                                                                    (text
                                                                    "Set initial_fuel and max_fuel at once"))
                                                                    ::
                                                                    uu___45 in
                                                                    (102,
                                                                    "force",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    (text
                                                                    "Force checking the files given as arguments even if they have valid checked files"))
                                                                    ::
                                                                    uu___44 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "print_in_place",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    (text
                                                                    "Parses and prettyprints in place the files included on the command line"))
                                                                    ::
                                                                    uu___43 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "print",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    (text
                                                                    "Parses and prettyprints the files included on the command line"))
                                                                    ::
                                                                    uu___42 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "include",
                                                                    (ReverseAccumulated
                                                                    (PathStr
                                                                    "dir")),
                                                                    (text
                                                                    "A directory in which to search for files included on the command line"))
                                                                    ::
                                                                    uu___41 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "ide_id_info_off",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    (text
                                                                    "Disable identifier tables in IDE mode (temporary workaround useful in Steel)"))
                                                                    ::
                                                                    uu___40 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "ide",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    (text
                                                                    "JSON-based interactive mode for IDEs (used by VSCode, emacs, neovim, etc.)"))
                                                                    ::
                                                                    uu___39 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "hint_info",
                                                                    (Const
                                                                    (Bool
                                                                    true)),
                                                                    (text
                                                                    "Print information regarding hints (deprecated; use --query_stats instead)"))
                                                                    ::
                                                                    uu___38 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "hint_file",
                                                                    (PathStr
                                                                    "path"),
                                                                    (text
                                                                    "Read/write hints to  path (instead of module-specific hints files; overrides hint_dir)"))
                                                                    ::
                                                                    uu___37 in
                                                                    (FStarC_Getopt.noshort,
                                                                    "hint_dir",
                                                                    (PostProcessed
                                                                    (pp_validate_dir,
                                                                    (PathStr
                                                                    "dir"))),
                                                                    (text
                                                                    "Read/write hints to  dir/module_name.hints (instead of placing hint-file alongside source file)"))
                                                                    ::
                                                                    uu___36 in
                                                                  (FStarC_Getopt.noshort,
                                                                    "hide_uvar_nums",
                                                                    (
                                                                    Const
                                                                    (Bool
                                                                    true)),
                                                                    (
                                                                    text
                                                                    "Don't print unification variable numbers"))
                                                                    ::
                                                                    uu___35 in
                                                                (FStarC_Getopt.noshort,
                                                                  "message_format",
                                                                  (EnumStr
                                                                    ["human";
                                                                    "json";
                                                                    "github";
                                                                    "auto"]),
                                                                  (text
                                                                    "Format of the messages emitted by F*. Using 'auto' will use human messages unless the variable GITHUB_ACTIONS is non-empty, in which case 'github' is used (default `auto`)."))
                                                                  :: uu___34 in
                                                              (FStarC_Getopt.noshort,
                                                                "expose_interfaces",
                                                                (Const
                                                                   (Bool true)),
                                                                (text
                                                                   "Explicitly break the abstraction imposed by the interface of any implementation file that appears on the command line (use with care!)"))
                                                                :: uu___33 in
                                                            (FStarC_Getopt.noshort,
                                                              "extract_namespace",
                                                              (Accumulated
                                                                 (PostProcessed
                                                                    (pp_lowercase,
                                                                    (SimpleStr
                                                                    "namespace name")))),
                                                              (text
                                                                 "Deprecated: use --extract instead; Only extract modules in the specified namespace"))
                                                              :: uu___32 in
                                                          (FStarC_Getopt.noshort,
                                                            "extract_module",
                                                            (Accumulated
                                                               (PostProcessed
                                                                  (pp_lowercase,
                                                                    (
                                                                    SimpleStr
                                                                    "module_name")))),
                                                            (text
                                                               "Deprecated: use --extract instead; Only extract the specified modules (instead of the possibly-partial dependency graph)"))
                                                            :: uu___31 in
                                                        (FStarC_Getopt.noshort,
                                                          "extract",
                                                          (Accumulated
                                                             (SimpleStr
                                                                "One or more semicolon separated occurrences of '[TargetName:]ModuleSelector'")),
                                                          (text
                                                             "Extract only those modules whose names or namespaces match the provided options. 'TargetName' ranges over {OCaml, krml, FSharp, Plugin, PluginNoLib, Extension}. A 'ModuleSelector' is a space or comma-separated list of '[+|-]( * | namespace | module)'. For example --extract 'OCaml:A -A.B' --extract 'krml:A -A.C' --extract '*' means for OCaml, extract everything in the A namespace only except A.B; for krml, extract everything in the A namespace only except A.C; for everything else, extract everything. Note, the '+' is optional: --extract '+A' and --extract 'A' mean the same thing. Note also that '--extract A' applies both to a module named 'A' and to any module in the 'A' namespace Multiple uses of this option accumulate, e.g., --extract A --extract B is interpreted as --extract 'A B'."))
                                                          :: uu___30 in
                                                      (FStarC_Getopt.noshort,
                                                        "ext",
                                                        (PostProcessed
                                                           ((fun o ->
                                                               let parse_ext
                                                                 s =
                                                                 let exts =
                                                                   FStarC_Util.split
                                                                    s ";" in
                                                                 FStarC_List.collect
                                                                   (fun s1 ->
                                                                    match 
                                                                    FStarC_Util.split
                                                                    s1 "="
                                                                    with
                                                                    | 
                                                                    k::v::[]
                                                                    ->
                                                                    [(k, v)]
                                                                    | 
                                                                    uu___30
                                                                    ->
                                                                    [
                                                                    (s1, "1")])
                                                                   exts in
                                                               (let uu___31 =
                                                                  let uu___32
                                                                    =
                                                                    as_comma_string_list
                                                                    o in
                                                                  FStarC_List.collect
                                                                    parse_ext
                                                                    uu___32 in
                                                                FStarC_List.iter
                                                                  (fun
                                                                    uu___32
                                                                    ->
                                                                    match uu___32
                                                                    with
                                                                    | 
                                                                    (k, v) ->
                                                                    FStarC_Options_Ext.set
                                                                    k v)
                                                                  uu___31);
                                                               o),
                                                             (ReverseAccumulated
                                                                (SimpleStr
                                                                   "extension knobs")))),
                                                        (text
                                                           "These options are set in extensions option map. Keys are usually namespaces separated by \":\". E.g., 'pulse:verbose=1;my:extension:option=xyz;foo:bar=baz'. These options are typically interpreted by extensions. Any later use of --ext over the same key overrides the old value. An entry 'e' that is not of the form 'a=b' is treated as 'e=1', i.e., 'e' associated with string \"1\"."))
                                                        :: uu___29 in
                                                    (FStarC_Getopt.noshort,
                                                      "error_contexts",
                                                      BoolStr,
                                                      (text
                                                         "Print context information for each error or warning raised (default false)"))
                                                      :: uu___28 in
                                                  (FStarC_Getopt.noshort,
                                                    "eager_subtyping",
                                                    (Const (Bool true)),
                                                    (text
                                                       "Try to solve subtyping constraints at each binder (loses precision but may be slightly more efficient)"))
                                                    :: uu___27 in
                                                (FStarC_Getopt.noshort,
                                                  "dump_module",
                                                  (Accumulated
                                                     (SimpleStr "module_name")),
                                                  (text
                                                     "Print out this module as it passes through the compiler pipeline"))
                                                  :: uu___26 in
                                              (FStarC_Getopt.noshort,
                                                "dump_ast",
                                                (Const (Bool true)),
                                                (text
                                                   "Dump the surface AST of the given file."))
                                                :: uu___25 in
                                            (FStarC_Getopt.noshort,
                                              "detail_hint_replay",
                                              (Const (Bool true)),
                                              (text
                                                 "Emit a detailed report for proof whose unsat core fails to replay"))
                                              :: uu___24 in
                                          (FStarC_Getopt.noshort,
                                            "detail_errors",
                                            (Const (Bool true)),
                                            (text
                                               "Emit a detailed error report by asking the SMT solver many queries; will take longer"))
                                            :: uu___23 in
                                        uu___21 :: uu___22 in
                                      uu___19 :: uu___20 in
                                    (FStarC_Getopt.noshort,
                                      "debug_all_modules",
                                      (Const (Bool true)),
                                      (text
                                         "Enable to make the effect of --debug apply to every module processed by the compiler, including dependencies."))
                                      :: uu___18 in
                                  (FStarC_Getopt.noshort, "debug_all",
                                    (PostProcessed
                                       ((fun o ->
                                           match o with
                                           | Bool (true) ->
                                               (FStarC_Debug.set_debug_all ();
                                                o)
                                           | uu___18 ->
                                               FStarC_Effect.failwith "?"),
                                         (Const (Bool true)))),
                                    (text
                                       "Enable all debug toggles. WARNING: this will cause a lot of output!"))
                                    :: uu___17 in
                                (FStarC_Getopt.noshort, "debug",
                                  (PostProcessed
                                     ((fun o ->
                                         let keys = as_comma_string_list o in
                                         FStarC_Debug.enable_toggles keys; o),
                                       (ReverseAccumulated
                                          (SimpleStr "debug toggles")))),
                                  (text
                                     "Enable specific debug toggles (comma-separated list of debug keys). You can use a '-' at the beginning of a toggle to disable it instead."))
                                  :: uu___16 in
                              (100, "",
                                (PostProcessed
                                   ((fun o -> FStarC_Debug.enable (); o),
                                     (Const (Bool true)))),
                                (text
                                   "Enable general debugging, i.e. increase verbosity."))
                                :: uu___15 in
                            (FStarC_Getopt.noshort, "codegen-lib",
                              (Accumulated (SimpleStr "namespace")),
                              (text
                                 "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)"))
                              :: uu___14 in
                          (FStarC_Getopt.noshort, "codegen",
                            (EnumStr
                               ["OCaml";
                               "FSharp";
                               "krml";
                               "Plugin";
                               "PluginNoLib";
                               "Extension"]),
                            (text
                               "Generate code for further compilation to executable code, or build a compiler plugin"))
                            :: uu___13 in
                        (FStarC_Getopt.noshort, "no_cmi",
                          (Const (Bool true)),
                          (text
                             "Disable inlining across module interfaces during extraction (aka. cross-module inlining). Enabled by default."))
                          :: uu___12 in
                      (FStarC_Getopt.noshort, "print_cache_version",
                        (Const (Bool true)),
                        (text
                           "Print the version for .checked files and exit."))
                        :: uu___11 in
                    (FStarC_Getopt.noshort, "cache_off", (Const (Bool true)),
                      (text "Do not read or write any .checked files")) ::
                      uu___10 in
                  (FStarC_Getopt.noshort, "cache_dir",
                    (PostProcessed
                       ((fun uu___10 ->
                           match uu___10 with
                           | Path s -> (FStarC_Find.set_cache_dir s; Unset)),
                         (PathStr "dir"))),
                    (text
                       "Read and write .checked and .checked.lax in directory dir"))
                    :: uu___9 in
                (99, "cache_checked_modules", (Const (Bool true)),
                  (text
                     "Write a '.checked' file for each module after verification."))
                  :: uu___8 in
              (FStarC_Getopt.noshort, "already_cached",
                (ReverseAccumulated
                   (SimpleStr
                      "One or more space-separated occurrences of '[+|-]( * | namespace | module)'")),
                (text
                   "Expects all modules whose names or namespaces match the provided options to already have valid .checked files in the include path"))
                :: uu___7 in
            (FStarC_Getopt.noshort, "disallow_unification_guards", BoolStr,
              (text
                 "Fail if the SMT guard are produced when the tactic engine re-checks solutions produced by the unifier (default 'false')"))
              :: uu___6 in
          (FStarC_Getopt.noshort, "compat_pre_typed_indexed_effects",
            (Const (Bool true)),
            (text "Retain untyped indexed effects implicits")) :: uu___5 in
        (FStarC_Getopt.noshort, "compat_pre_core", (IntStr "0, 1, 2"),
          (text
             "Retain behavior of the tactic engine prior to the introduction of FStarC.TypeChecker.Core (0 is most permissive, 2 is least permissive)"))
          :: uu___4 in
      (FStarC_Getopt.noshort, "admit_except",
        (WithSideEffect
           ((fun uu___4 ->
               if warn_unsafe
               then option_warning_callback "admit_except"
               else ()), (SimpleStr "[symbol|(symbol, id)]"))),
        (text
           "Admit all queries, except those with label ( symbol,  id))(e.g. --admit_except '(FStar.Fin.pigeonhole, 1)' or --admit_except FStar.Fin.pigeonhole)"))
        :: uu___3 in
    (FStarC_Getopt.noshort, "admit_smt_queries",
      (WithSideEffect
         ((fun uu___3 ->
             if warn_unsafe
             then option_warning_callback "admit_smt_queries"
             else ()), BoolStr)),
      (text "Admit SMT queries, unsafe! (default 'false')")) :: uu___2 in
  (FStarC_Getopt.noshort, "abort_on",
    (PostProcessed
       ((fun uu___2 ->
           match uu___2 with
           | Int x -> (FStarC_Effect.op_Colon_Equals abort_counter x; Int x)
           | x -> FStarC_Effect.failwith "?"),
         (IntStr "non-negative integer"))),
    (text
       "Abort on the n-th error or warning raised. Useful in combination with --trace_error. Count starts at 1, use 0 to disable. (default 0)"))
    :: uu___
let specs (warn_unsafe : Prims.bool) :
  (FStarC_Getopt.opt * FStar_Pprint.document) Prims.list=
  let uu___ = specs_with_types warn_unsafe in
  FStarC_List.map
    (fun uu___2 ->
       match uu___2 with
       | (short, long, typ, doc) ->
           let uu___3 =
             let uu___4 =
               let uu___5 = arg_spec_of_opt_type long typ in
               (short, long, uu___5) in
             mk_spec uu___4 in
           (uu___3, doc)) uu___
let settable (uu___ : Prims.string) : Prims.bool=
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
  | "lang_extensions" -> true
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
  | "record_hints" -> true
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
  | "stats" -> true
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
let all_specs : (FStarC_Getopt.opt * FStar_Pprint.document) Prims.list=
  specs true
let all_specs_getopt : FStarC_Getopt.opt Prims.list=
  FStarC_List.map FStar_Pervasives_Native.fst all_specs
let all_specs_with_types :
  (FStarC_BaseTypes.char * Prims.string * opt_type * FStar_Pprint.document)
    Prims.list=
  specs_with_types true
let settable_specs :
  ((FStarC_BaseTypes.char * Prims.string * unit FStarC_Getopt.opt_variant) *
    FStar_Pprint.document) Prims.list=
  FStarC_List.map
    (fun spec ->
       let uu___ = spec in
       match uu___ with
       | ((c, x, h), doc) ->
           if settable x
           then spec
           else
             (let h' =
                match h with
                | FStarC_Getopt.ZeroArgs uu___3 ->
                    FStarC_Getopt.ZeroArgs
                      ((fun uu___4 -> FStarC_Effect.raise (NotSettable x)))
                | FStarC_Getopt.OneArg (uu___3, k) ->
                    FStarC_Getopt.OneArg
                      (((fun s -> FStarC_Effect.raise (NotSettable x))), k) in
              ((c, x, h'), doc))) all_specs
let help_for_option (s : Prims.string) :
  FStar_Pprint.document FStar_Pervasives_Native.option=
  let uu___ =
    FStarC_List.filter
      (fun uu___2 ->
         match uu___2 with | ((uu___3, x, uu___4), uu___5) -> x = s)
      all_specs in
  match uu___ with
  | [] -> FStar_Pervasives_Native.None
  | o::uu___2 ->
      let uu___3 = usage_for o in FStar_Pervasives_Native.Some uu___3
let uu___2 :
  (((unit -> FStarC_Getopt.parse_cmdline_res) -> unit) *
    (unit -> FStarC_Getopt.parse_cmdline_res))=
  let callback = FStarC_Effect.mk_ref FStar_Pervasives_Native.None in
  let set1 f =
    FStarC_Effect.op_Colon_Equals callback (FStar_Pervasives_Native.Some f) in
  let call uu___ =
    let uu___3 = FStarC_Effect.op_Bang callback in
    match uu___3 with
    | FStar_Pervasives_Native.None ->
        FStarC_Effect.failwith "Error flags callback not yet set"
    | FStar_Pervasives_Native.Some f -> f () in
  (set1, call)
let set_error_flags_callback_aux :
  (unit -> FStarC_Getopt.parse_cmdline_res) -> unit=
  match uu___2 with
  | (set_error_flags_callback_aux1, set_error_flags) ->
      set_error_flags_callback_aux1
let set_error_flags : unit -> FStarC_Getopt.parse_cmdline_res=
  match uu___2 with
  | (set_error_flags_callback_aux1, set_error_flags1) -> set_error_flags1
let set_error_flags_callback :
  (unit -> FStarC_Getopt.parse_cmdline_res) -> unit=
  set_error_flags_callback_aux
let display_usage (uu___ : unit) : unit= display_usage_aux all_specs
let fstar_bin_directory : Prims.string= FStarC_Util.get_exec_dir ()
let file_list_ : Prims.string Prims.list FStarC_Effect.ref=
  FStarC_Effect.mk_ref []
let rec parse_filename_arg (specs1 : FStarC_Getopt.opt Prims.list)
  (enable_filenames : Prims.bool) (arg : Prims.string) :
  FStarC_Getopt.parse_cmdline_res=
  if FStarC_Util.starts_with arg "@"
  then
    let filename = FStarC_Util.substring_from arg Prims.int_one in
    let lines = FStarC_Util.file_get_lines filename in
    FStarC_Getopt.parse_list specs1
      (parse_filename_arg specs1 enable_filenames) lines
  else
    (if enable_filenames
     then
       (let uu___4 =
          let uu___5 = FStarC_Effect.op_Bang file_list_ in
          FStarC_List.op_At uu___5 [arg] in
        FStarC_Effect.op_Colon_Equals file_list_ uu___4)
     else ();
     FStarC_Getopt.Success)
let parsed_args_state :
  history1 FStar_Pervasives_Native.option FStarC_Effect.ref=
  FStarC_Effect.mk_ref FStar_Pervasives_Native.None
let parse_cmd_line (uu___ : unit) :
  (FStarC_Getopt.parse_cmdline_res * Prims.string Prims.list)=
  let res =
    FStarC_Getopt.parse_cmdline all_specs_getopt
      (parse_filename_arg all_specs_getopt true) in
  let res1 = if res = FStarC_Getopt.Success then set_error_flags () else res in
  (let paths = let uu___4 = get_option "include" in as_list as_string uu___4 in
   FStarC_List.iter
     (fun p ->
        let uu___5 = FStarC_Effect.op_Bang check_include_dir in uu___5 p)
     paths;
   (let uu___6 =
      let uu___7 = FStarC_Find.get_include_path () in
      FStarC_List.op_At uu___7 paths in
    FStarC_Find.set_include_path uu___6));
  (match () with
   | () ->
       ((let uu___5 =
           let uu___6 = snapshot_all () in
           FStar_Pervasives_Native.Some uu___6 in
         FStarC_Effect.op_Colon_Equals parsed_args_state uu___5);
        (let uu___5 = FStarC_Effect.op_Bang file_list_ in (res1, uu___5))))
let file_list (uu___ : unit) : Prims.string Prims.list=
  FStarC_Effect.op_Bang file_list_
let restore_cmd_line_options (should_clear : Prims.bool) :
  FStarC_Getopt.parse_cmdline_res=
  let old_verify_module = get_verify_module () in
  if should_clear then clear () else init ();
  (let uu___3 = FStarC_Effect.op_Bang parsed_args_state in
   match uu___3 with
   | FStar_Pervasives_Native.None ->
       FStarC_Effect.failwith
         "impossible: restore_cmd_line_options before initial parsing"
   | FStar_Pervasives_Native.Some h ->
       (restore_all h;
        (let uu___6 =
           let uu___7 =
             let uu___8 =
               FStarC_List.map (fun uu___9 -> String uu___9)
                 old_verify_module in
             List uu___8 in
           ("verify_module", uu___7) in
         set_option' uu___6);
        FStarC_Getopt.Success))
let with_restored_cmd_line_options (f : unit -> 'a) : 'a=
  let snap = snapshot_all () in
  let h = FStarC_Effect.op_Bang history in
  let uu___ = restore_cmd_line_options true in
  FStarC_Util.finally
    (fun uu___3 -> FStarC_Effect.op_Colon_Equals history h; restore_all snap)
    f
let module_name_of_file_name (f : Prims.string) : Prims.string=
  let f1 = FStarC_Filepath.basename f in
  let f2 =
    FStarC_String.substring f1 Prims.int_zero
      (((FStarC_String.length f1) -
          (FStarC_String.length (FStarC_Filepath.get_file_extension f1)))
         - Prims.int_one) in
  FStarC_String.lowercase f2
let should_check (m : Prims.string) : Prims.bool=
  let l = get_verify_module () in
  FStarC_List.contains (FStarC_String.lowercase m) l
let should_verify (m : Prims.string) : Prims.bool=
  let uu___ = let uu___3 = get_lax () in Prims.op_Negation uu___3 in
  if uu___ then should_check m else false
let should_check_file (fn : Prims.string) : Prims.bool=
  let uu___ = module_name_of_file_name fn in should_check uu___
let should_verify_file (fn : Prims.string) : Prims.bool=
  let uu___ = module_name_of_file_name fn in should_verify uu___
let module_name_eq (m1 : Prims.string) (m2 : Prims.string) : Prims.bool=
  (FStarC_String.lowercase m1) = (FStarC_String.lowercase m2)
let should_print_message (m : Prims.string) : Prims.bool=
  let uu___ = should_verify m in if uu___ then m <> "Prims" else false
let custom_prims (uu___ : unit) :
  Prims.string FStar_Pervasives_Native.option= get_prims ()
let path_of_text (text : Prims.string) : Prims.string Prims.list=
  FStarC_String.split [46] text
let parse_settings (ns : Prims.string Prims.list) :
  (Prims.string Prims.list * Prims.bool) Prims.list=
  let cache = FStarC_SMap.create (Prims.of_int (31)) in
  let with_cache f s =
    let uu___ = FStarC_SMap.try_find cache s in
    match uu___ with
    | FStar_Pervasives_Native.Some s1 -> s1
    | FStar_Pervasives_Native.None ->
        let res = f s in (FStarC_SMap.add cache s res; res) in
  let parse_one_setting s =
    if s = "*"
    then ([], true)
    else
      if s = "-*"
      then ([], false)
      else
        if FStarC_Util.starts_with s "-"
        then
          (let path =
             let uu___4 = FStarC_Util.substring_from s Prims.int_one in
             path_of_text uu___4 in
           (path, false))
        else
          (let s1 =
             if FStarC_Util.starts_with s "+"
             then FStarC_Util.substring_from s Prims.int_one
             else s in
           ((path_of_text s1), true)) in
  let uu___ =
    FStarC_List.collect
      (fun s ->
         let s1 = FStarC_Util.trim_string s in
         if s1 = ""
         then []
         else
           with_cache
             (fun s2 ->
                let s3 = FStarC_Util.replace_char s2 32 44 in
                let uu___4 =
                  let uu___5 =
                    FStarC_List.concatMap
                      (fun s4 -> FStarC_Util.split s4 ",")
                      (FStarC_Util.splitlines s3) in
                  FStarC_List.filter (fun s4 -> s4 <> "") uu___5 in
                FStarC_List.map parse_one_setting uu___4) s1) ns in
  FStarC_List.rev uu___
let admit_smt_queries (uu___ : unit) : Prims.bool= get_admit_smt_queries ()
let admit_except (uu___ : unit) :
  Prims.string FStar_Pervasives_Native.option= get_admit_except ()
let compat_pre_core_should_register (uu___ : unit) : Prims.bool=
  let uu___3 = get_compat_pre_core () in
  match uu___3 with
  | FStar_Pervasives_Native.Some uu___4 when uu___4 = Prims.int_zero -> false
  | uu___4 -> true
let compat_pre_core_should_check (uu___ : unit) : Prims.bool=
  let uu___3 = get_compat_pre_core () in
  match uu___3 with
  | FStar_Pervasives_Native.Some uu___4 when uu___4 = Prims.int_zero -> false
  | FStar_Pervasives_Native.Some uu___4 when uu___4 = Prims.int_one -> false
  | uu___4 -> true
let compat_pre_core_set (uu___ : unit) : Prims.bool=
  let uu___3 = get_compat_pre_core () in
  match uu___3 with | FStar_Pervasives_Native.None -> false | uu___4 -> true
let compat_pre_typed_indexed_effects (uu___ : unit) : Prims.bool=
  get_compat_pre_typed_indexed_effects ()
let disallow_unification_guards (uu___ : unit) : Prims.bool=
  get_disallow_unification_guards ()
let cache_checked_modules (uu___ : unit) : Prims.bool=
  get_cache_checked_modules ()
let cache_off (uu___ : unit) : Prims.bool= get_cache_off ()
let print_cache_version (uu___ : unit) : Prims.bool=
  get_print_cache_version ()
let cmi (uu___ : unit) : Prims.bool=
  let uu___3 = get_no_cmi () in Prims.op_Negation uu___3
let parse_codegen (uu___ : Prims.string) :
  codegen_t FStar_Pervasives_Native.option=
  match uu___ with
  | "OCaml" -> FStar_Pervasives_Native.Some OCaml
  | "FSharp" -> FStar_Pervasives_Native.Some FSharp
  | "krml" -> FStar_Pervasives_Native.Some Krml
  | "Plugin" -> FStar_Pervasives_Native.Some Plugin
  | "PluginNoLib" -> FStar_Pervasives_Native.Some PluginNoLib
  | "Extension" -> FStar_Pervasives_Native.Some Extension
  | uu___3 -> FStar_Pervasives_Native.None
let print_codegen (uu___ : codegen_t) : Prims.string=
  match uu___ with
  | OCaml -> "OCaml"
  | FSharp -> "FSharp"
  | Krml -> "krml"
  | Plugin -> "Plugin"
  | PluginNoLib -> "PluginNoLib"
  | Extension -> "Extension"
let codegen (uu___ : unit) : codegen_t FStar_Pervasives_Native.option=
  let uu___3 = get_codegen () in
  FStarC_Option.map
    (fun s -> FStar_Pervasives_Native.__proj__Some__item__v (parse_codegen s))
    uu___3
let codegen_libs (uu___ : unit) : Prims.string Prims.list Prims.list=
  let uu___3 = get_codegen_lib () in
  FStarC_List.map (fun x -> FStarC_Util.split x ".") uu___3
let profile_group_by_decl (uu___ : unit) : Prims.bool=
  get_profile_group_by_decl ()
let defensive (uu___ : unit) : Prims.bool=
  let uu___3 = get_defensive () in uu___3 <> "no"
let defensive_error (uu___ : unit) : Prims.bool=
  let uu___3 = get_defensive () in uu___3 = "error"
let defensive_abort (uu___ : unit) : Prims.bool=
  let uu___3 = get_defensive () in uu___3 = "abort"
let dep (uu___ : unit) : Prims.string FStar_Pervasives_Native.option=
  get_dep ()
let detail_errors (uu___ : unit) : Prims.bool= get_detail_errors ()
let detail_hint_replay (uu___ : unit) : Prims.bool= get_detail_hint_replay ()
let any_dump_module (uu___ : unit) : Prims.bool=
  let uu___3 = get_dump_module () in Prims.uu___is_Cons uu___3
let dump_ast (uu___ : unit) : Prims.bool= get_dump_ast ()
let dump_module (s : Prims.string) : Prims.bool=
  let uu___ = get_dump_module () in
  FStarC_List.existsb (module_name_eq s) uu___
let eager_subtyping (uu___ : unit) : Prims.bool= get_eager_subtyping ()
let error_contexts (uu___ : unit) : Prims.bool= get_error_contexts ()
let expose_interfaces (uu___ : unit) : Prims.bool= get_expose_interfaces ()
let interactive (uu___ : unit) : Prims.bool= get_ide ()
let message_format (uu___ : unit) : message_format_t=
  let uu___3 = get_message_format () in
  match uu___3 with
  | "auto" ->
      let uu___4 = interactive () in
      if uu___4
      then Human
      else
        (let uu___6 =
           FStarC_Util.expand_environment_variable "GITHUB_ACTIONS" in
         match uu___6 with
         | FStar_Pervasives_Native.None -> Human
         | FStar_Pervasives_Native.Some "" -> Human
         | FStar_Pervasives_Native.Some uu___7 -> Github)
  | "human" -> Human
  | "json" -> Json
  | "github" -> Github
  | illegal ->
      FStarC_Effect.failwith
        (FStarC_String.op_Hat
           "print_issue: option `message_format` was expected to be `human` or `json`, not `"
           (FStarC_String.op_Hat illegal
              "`. This should be impossible: `message_format` was supposed to be validated."))
let force (uu___ : unit) : Prims.bool= get_force ()
let help (uu___ : unit) : Prims.bool= get_help ()
let hide_uvar_nums (uu___ : unit) : Prims.bool= get_hide_uvar_nums ()
let hint_info (uu___ : unit) : Prims.bool=
  let uu___3 = get_hint_info () in
  if uu___3 then true else get_query_stats ()
let hint_dir (uu___ : unit) : Prims.string FStar_Pervasives_Native.option=
  get_hint_dir ()
let hint_file (uu___ : unit) : Prims.string FStar_Pervasives_Native.option=
  get_hint_file ()
let hint_file_for_src (src_filename : Prims.string) : Prims.string=
  let uu___ = hint_file () in
  match uu___ with
  | FStar_Pervasives_Native.Some fn -> fn
  | FStar_Pervasives_Native.None ->
      let file_name =
        let uu___3 = hint_dir () in
        match uu___3 with
        | FStar_Pervasives_Native.Some dir ->
            FStarC_Util.concat_dir_filename dir
              (FStarC_Filepath.basename src_filename)
        | uu___4 -> src_filename in
      FStarC_Format.fmt1 "%s.hints" file_name
let ide (uu___ : unit) : Prims.bool= get_ide ()
let ide_id_info_off (uu___ : unit) : Prims.bool= get_ide_id_info_off ()
let ide_file_name_st :
  ((Prims.string -> unit) *
    (unit -> Prims.string FStar_Pervasives_Native.option))=
  let v = FStarC_Effect.mk_ref FStar_Pervasives_Native.None in
  let set1 f =
    let uu___ = FStarC_Effect.op_Bang v in
    match uu___ with
    | FStar_Pervasives_Native.None ->
        FStarC_Effect.op_Colon_Equals v (FStar_Pervasives_Native.Some f)
    | FStar_Pervasives_Native.Some uu___3 ->
        FStarC_Effect.failwith "ide_file_name_st already set" in
  let get uu___ = FStarC_Effect.op_Bang v in (set1, get)
let set_ide_filename : Prims.string -> unit=
  FStar_Pervasives_Native.fst ide_file_name_st
let ide_filename : unit -> Prims.string FStar_Pervasives_Native.option=
  FStar_Pervasives_Native.snd ide_file_name_st
let print (uu___ : unit) : Prims.bool= get_print ()
let print_in_place (uu___ : unit) : Prims.bool= get_print_in_place ()
let initial_fuel (uu___ : unit) : Prims.int=
  let uu___3 = get_initial_fuel () in
  let uu___4 = get_max_fuel () in Prims.min uu___3 uu___4
let initial_ifuel (uu___ : unit) : Prims.int=
  let uu___3 = get_initial_ifuel () in
  let uu___4 = get_max_ifuel () in Prims.min uu___3 uu___4
let lang_extensions (uu___ : unit) : Prims.string Prims.list=
  get_lang_extensions ()
let lax (uu___ : unit) : Prims.bool= get_lax ()
let load (uu___ : unit) : Prims.string Prims.list= get_load ()
let load_cmxs (uu___ : unit) : Prims.string Prims.list= get_load_cmxs ()
let log_queries (uu___ : unit) : Prims.bool= get_log_queries ()
let log_failing_queries (uu___ : unit) : Prims.bool=
  get_log_failing_queries ()
let keep_query_captions (uu___ : unit) : Prims.bool=
  let uu___3 = get_keep_query_captions () in
  if uu___3
  then
    let uu___4 = log_queries () in
    (if uu___4 then true else log_failing_queries ())
  else false
let log_types (uu___ : unit) : Prims.bool= get_log_types ()
let max_fuel (uu___ : unit) : Prims.int= get_max_fuel ()
let max_ifuel (uu___ : unit) : Prims.int= get_max_ifuel ()
let no_extract (s : Prims.string) : Prims.bool=
  let uu___ = get_no_extract () in
  FStarC_List.existsb (module_name_eq s) uu___
let normalize_pure_terms_for_extraction (uu___ : unit) : Prims.bool=
  get_normalize_pure_terms_for_extraction ()
let no_location_info (uu___ : unit) : Prims.bool= get_no_location_info ()
let no_prelude (uu___ : unit) : Prims.bool= get_no_prelude ()
let no_plugins (uu___ : unit) : Prims.bool= get_no_plugins ()
let no_smt (uu___ : unit) : Prims.bool= get_no_smt ()
let op_Bar_Bar_Bar (o : 'uuuuu FStar_Pervasives_Native.option)
  (x : 'uuuuu FStar_Pervasives_Native.option) :
  'uuuuu FStar_Pervasives_Native.option=
  match o with
  | FStar_Pervasives_Native.None -> x
  | FStar_Pervasives_Native.Some uu___ -> o
let output_to (uu___ : unit) : Prims.string FStar_Pervasives_Native.option=
  get_output_to ()
let krmloutput (uu___ : unit) : Prims.string FStar_Pervasives_Native.option=
  let uu___3 = get_krmloutput () in
  let uu___4 = output_to () in op_Bar_Bar_Bar uu___3 uu___4
let output_deps_to (uu___ : unit) :
  Prims.string FStar_Pervasives_Native.option=
  let uu___3 = get_output_deps_to () in
  let uu___4 = output_to () in op_Bar_Bar_Bar uu___3 uu___4
let ugly (uu___ : unit) : Prims.bool= get_ugly ()
let print_bound_var_types (uu___ : unit) : Prims.bool=
  get_print_bound_var_types ()
let print_effect_args (uu___ : unit) : Prims.bool= get_print_effect_args ()
let print_expected_failures (uu___ : unit) : Prims.bool=
  get_print_expected_failures ()
let print_implicits (uu___ : unit) : Prims.bool= get_print_implicits ()
let print_real_names (uu___ : unit) : Prims.bool=
  let uu___3 = get_prn () in if uu___3 then true else get_print_full_names ()
let print_universes (uu___ : unit) : Prims.bool= get_print_universes ()
let print_z3_statistics (uu___ : unit) : Prims.bool=
  get_print_z3_statistics ()
let proof_recovery (uu___ : unit) : Prims.bool= get_proof_recovery ()
let quake_lo (uu___ : unit) : Prims.int= get_quake_lo ()
let quake_hi (uu___ : unit) : Prims.int= get_quake_hi ()
let quake_keep (uu___ : unit) : Prims.bool= get_quake_keep ()
let query_cache (uu___ : unit) : Prims.bool= get_query_cache ()
let query_stats (uu___ : unit) : Prims.bool= get_query_stats ()
let read_checked_file (uu___ : unit) :
  Prims.string FStar_Pervasives_Native.option= get_read_checked_file ()
let list_plugins (uu___ : unit) : Prims.bool= get_list_plugins ()
let expand_include (uu___ : unit) :
  Prims.string FStar_Pervasives_Native.option= get_expand_include ()
let locate (uu___ : unit) : Prims.bool= get_locate ()
let locate_lib (uu___ : unit) : Prims.bool= get_locate_lib ()
let locate_ocaml (uu___ : unit) : Prims.bool= get_locate_ocaml ()
let locate_file (uu___ : unit) : Prims.string FStar_Pervasives_Native.option=
  get_locate_file ()
let locate_z3 (uu___ : unit) : Prims.string FStar_Pervasives_Native.option=
  get_locate_z3 ()
let read_krml_file (uu___ : unit) :
  Prims.string FStar_Pervasives_Native.option= get_read_krml_file ()
let record_hints (uu___ : unit) : Prims.bool= get_record_hints ()
let record_options (uu___ : unit) : Prims.bool= get_record_options ()
let retry (uu___ : unit) : Prims.bool= get_retry ()
let reuse_hint_for (uu___ : unit) :
  Prims.string FStar_Pervasives_Native.option= get_reuse_hint_for ()
let report_assumes (uu___ : unit) :
  Prims.string FStar_Pervasives_Native.option= get_report_assumes ()
let silent (uu___ : unit) : Prims.bool= get_silent ()
let smt (uu___ : unit) : Prims.string FStar_Pervasives_Native.option=
  get_smt ()
let smtencoding_elim_box (uu___ : unit) : Prims.bool=
  get_smtencoding_elim_box ()
let smtencoding_nl_arith_native (uu___ : unit) : Prims.bool=
  let uu___3 = get_smtencoding_nl_arith_repr () in uu___3 = "native"
let smtencoding_nl_arith_wrapped (uu___ : unit) : Prims.bool=
  let uu___3 = get_smtencoding_nl_arith_repr () in uu___3 = "wrapped"
let smtencoding_nl_arith_default (uu___ : unit) : Prims.bool=
  let uu___3 = get_smtencoding_nl_arith_repr () in uu___3 = "boxwrap"
let smtencoding_l_arith_native (uu___ : unit) : Prims.bool=
  let uu___3 = get_smtencoding_l_arith_repr () in uu___3 = "native"
let smtencoding_l_arith_default (uu___ : unit) : Prims.bool=
  let uu___3 = get_smtencoding_l_arith_repr () in uu___3 = "boxwrap"
let smtencoding_valid_intro (uu___ : unit) : Prims.bool=
  get_smtencoding_valid_intro ()
let smtencoding_valid_elim (uu___ : unit) : Prims.bool=
  get_smtencoding_valid_elim ()
let parse_split_queries (s : Prims.string) :
  split_queries_t FStar_Pervasives_Native.option=
  match s with
  | "no" -> FStar_Pervasives_Native.Some No
  | "on_failure" -> FStar_Pervasives_Native.Some OnFailure
  | "always" -> FStar_Pervasives_Native.Some Always
  | uu___ -> FStar_Pervasives_Native.None
let split_queries (uu___ : unit) : split_queries_t=
  let uu___3 =
    let uu___4 = get_split_queries () in parse_split_queries uu___4 in
  FStar_Pervasives_Native.__proj__Some__item__v uu___3
let stats (uu___ : unit) : Prims.bool= get_stats ()
let tactic_raw_binders (uu___ : unit) : Prims.bool= get_tactic_raw_binders ()
let tactics_failhard (uu___ : unit) : Prims.bool= get_tactics_failhard ()
let tactics_info (uu___ : unit) : Prims.bool= get_tactics_info ()
let tactic_trace (uu___ : unit) : Prims.bool= get_tactic_trace ()
let tactic_trace_d (uu___ : unit) : Prims.int= get_tactic_trace_d ()
let tactics_nbe (uu___ : unit) : Prims.bool= get_tactics_nbe ()
let tcnorm (uu___ : unit) : Prims.bool= get_tcnorm ()
let timing (uu___ : unit) : Prims.bool= get_timing ()
let trace_error (uu___ : unit) : Prims.bool= get_trace_error ()
let unthrottle_inductives (uu___ : unit) : Prims.bool=
  get_unthrottle_inductives ()
let unsafe_tactic_exec (uu___ : unit) : Prims.bool= get_unsafe_tactic_exec ()
let use_eq_at_higher_order (uu___ : unit) : Prims.bool=
  get_use_eq_at_higher_order ()
let use_hints (uu___ : unit) : Prims.bool= get_use_hints ()
let use_hint_hashes (uu___ : unit) : Prims.bool= get_use_hint_hashes ()
let use_native_tactics (uu___ : unit) :
  Prims.string FStar_Pervasives_Native.option= get_use_native_tactics ()
let use_tactics (uu___ : unit) : Prims.bool=
  let uu___3 = get_no_tactics () in Prims.op_Negation uu___3
let using_facts_from (uu___ : unit) :
  (Prims.string Prims.list * Prims.bool) Prims.list=
  let uu___3 = get_using_facts_from () in
  match uu___3 with
  | FStar_Pervasives_Native.None -> [([], true)]
  | FStar_Pervasives_Native.Some ns -> parse_settings ns
let warn_default_effects (uu___ : unit) : Prims.bool=
  get_warn_default_effects ()
let warn_error (uu___ : unit) : Prims.string=
  let uu___3 = get_warn_error () in FStarC_String.concat " " uu___3
let z3_cliopt (uu___ : unit) : Prims.string Prims.list= get_z3cliopt ()
let z3_smtopt (uu___ : unit) : Prims.string Prims.list= get_z3smtopt ()
let z3_refresh (uu___ : unit) : Prims.bool= get_z3refresh ()
let z3_rlimit (uu___ : unit) : Prims.int= get_z3rlimit ()
let z3_rlimit_factor (uu___ : unit) : Prims.int= get_z3rlimit_factor ()
let z3_seed (uu___ : unit) : Prims.int= get_z3seed ()
let z3_version (uu___ : unit) : Prims.string= get_z3version ()
let no_positivity (uu___ : unit) : Prims.bool= get_no_positivity ()
let use_nbe (uu___ : unit) : Prims.bool= get_use_nbe ()
let use_nbe_for_extraction (uu___ : unit) : Prims.bool=
  get_use_nbe_for_extraction ()
let trivial_pre_for_unannotated_effectful_fns (uu___ : unit) : Prims.bool=
  get_trivial_pre_for_unannotated_effectful_fns ()
let debug_keys (uu___ : unit) : Prims.string Prims.list=
  lookup_opt "debug" as_comma_string_list
let debug_all (uu___ : unit) : Prims.bool= lookup_opt "debug_all" as_bool
let debug_all_modules (uu___ : unit) : Prims.bool=
  lookup_opt "debug_all_modules" as_bool
let with_saved_options (f : unit -> 'a) : 'a=
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
       | FStar_Pervasives.Inl ex -> FStarC_Effect.raise ex)))
  else (push (); (let retv = f () in pop (); retv))
let module_matches_namespace_filter (m : Prims.string)
  (filter : Prims.string Prims.list) : Prims.bool=
  let m1 = FStarC_String.lowercase m in
  let setting = parse_settings filter in
  let m_components = path_of_text m1 in
  let rec matches_path m_components1 path =
    match (m_components1, path) with
    | (uu___, []) -> true
    | (m2::ms, p::ps) ->
        if m2 = (FStarC_String.lowercase p)
        then matches_path ms ps
        else false
    | uu___ -> false in
  let uu___ =
    FStarC_Util.try_find
      (fun uu___3 ->
         match uu___3 with | (path, uu___4) -> matches_path m_components path)
      setting in
  match uu___ with
  | FStar_Pervasives_Native.None -> false
  | FStar_Pervasives_Native.Some (uu___3, flag) -> flag
let matches_namespace_filter_opt (m : Prims.string)
  (uu___ : Prims.string Prims.list FStar_Pervasives_Native.option) :
  Prims.bool=
  match uu___ with
  | FStar_Pervasives_Native.None -> false
  | FStar_Pervasives_Native.Some filter ->
      module_matches_namespace_filter m filter
type parsed_extract_setting =
  {
  target_specific_settings: (codegen_t * Prims.string) Prims.list ;
  default_settings: Prims.string FStar_Pervasives_Native.option }
let __proj__Mkparsed_extract_setting__item__target_specific_settings
  (projectee : parsed_extract_setting) :
  (codegen_t * Prims.string) Prims.list=
  match projectee with
  | { target_specific_settings; default_settings;_} ->
      target_specific_settings
let __proj__Mkparsed_extract_setting__item__default_settings
  (projectee : parsed_extract_setting) :
  Prims.string FStar_Pervasives_Native.option=
  match projectee with
  | { target_specific_settings; default_settings;_} -> default_settings
let print_pes (pes : parsed_extract_setting) : Prims.string=
  let uu___ =
    let uu___3 =
      FStarC_List.map
        (fun uu___4 ->
           match uu___4 with
           | (tgt, s) -> FStarC_Format.fmt2 "(%s, %s)" (print_codegen tgt) s)
        pes.target_specific_settings in
    FStarC_String.concat "; " uu___3 in
  FStarC_Format.fmt2
    "{ target_specific_settings = %s;\n\t\n               default_settings = %s }"
    uu___
    (match pes.default_settings with
     | FStar_Pervasives_Native.None -> "None"
     | FStar_Pervasives_Native.Some s -> s)
let find_setting_for_target (tgt : codegen_t)
  (s : (codegen_t * Prims.string) Prims.list) :
  Prims.string FStar_Pervasives_Native.option=
  let uu___ =
    FStarC_Util.try_find
      (fun uu___3 -> match uu___3 with | (x, uu___4) -> x = tgt) s in
  match uu___ with
  | FStar_Pervasives_Native.Some (uu___3, s1) ->
      FStar_Pervasives_Native.Some s1
  | uu___3 -> FStar_Pervasives_Native.None
let extract_settings :
  unit -> parsed_extract_setting FStar_Pervasives_Native.option=
  let memo = FStarC_Effect.mk_ref (FStar_Pervasives_Native.None, false) in
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
          FStar_Pervasives_Native.Some
            (FStarC_String.op_Hat p01 (FStarC_String.op_Hat "," p11)) in
    let merge_target tgt =
      let uu___ =
        let uu___3 = find_setting_for_target tgt p0.target_specific_settings in
        let uu___4 = find_setting_for_target tgt p1.target_specific_settings in
        merge_setting uu___3 uu___4 in
      match uu___ with
      | FStar_Pervasives_Native.None -> []
      | FStar_Pervasives_Native.Some x -> [(tgt, x)] in
    let uu___ =
      FStarC_List.collect merge_target
        [OCaml; FSharp; Krml; Plugin; PluginNoLib; Extension] in
    {
      target_specific_settings = uu___;
      default_settings =
        (merge_setting p0.default_settings p1.default_settings)
    } in
  fun uu___ ->
    let uu___3 = FStarC_Effect.op_Bang memo in
    match uu___3 with
    | (result, set1) ->
        let fail msg =
          display_usage ();
          FStarC_Effect.failwith
            (FStarC_Format.fmt1
               "Could not parse '%s' passed to the --extract option" msg) in
        if set1
        then result
        else
          (let uu___5 = get_extract () in
           match uu___5 with
           | FStar_Pervasives_Native.None ->
               (FStarC_Effect.op_Colon_Equals memo
                  (FStar_Pervasives_Native.None, true);
                FStar_Pervasives_Native.None)
           | FStar_Pervasives_Native.Some extract_settings1 ->
               let parse_one_setting extract_setting =
                 let tgt_specific_settings =
                   FStarC_Util.split extract_setting ";" in
                 let split_one t_setting =
                   match FStarC_Util.split t_setting ":" with
                   | default_setting::[] ->
                       FStar_Pervasives.Inr
                         (FStarC_Util.trim_string default_setting)
                   | target::setting::[] ->
                       let target1 = FStarC_Util.trim_string target in
                       (match parse_codegen target1 with
                        | FStar_Pervasives_Native.None -> fail target1
                        | FStar_Pervasives_Native.Some tgt ->
                            FStar_Pervasives.Inl
                              (tgt, (FStarC_Util.trim_string setting))
                        | uu___6 -> fail t_setting) in
                 let settings =
                   FStarC_List.map split_one tgt_specific_settings in
                 let fail_duplicate msg tgt =
                   display_usage ();
                   FStarC_Effect.failwith
                     (FStarC_Format.fmt2
                        "Could not parse '%s'; multiple setting for %s target"
                        msg tgt) in
                 let pes =
                   FStarC_List.fold_right
                     (fun setting out ->
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
                              FStarC_Util.try_find
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
                                   default_settings = (out.default_settings)
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
                 FStarC_List.fold_right
                   (fun setting pes1 ->
                      let uu___6 = parse_one_setting setting in
                      merge_parsed_extract_settings pes1 uu___6)
                   extract_settings1 empty_pes in
               (FStarC_Effect.op_Colon_Equals memo
                  ((FStar_Pervasives_Native.Some pes), true);
                FStar_Pervasives_Native.Some pes))
let should_extract (m : Prims.string) (tgt : codegen_t) : Prims.bool=
  let m1 = FStarC_String.lowercase m in
  if m1 = "prims"
  then false
  else
    (let uu___3 = extract_settings () in
     match uu___3 with
     | FStar_Pervasives_Native.Some pes ->
         ((let uu___5 =
             let uu___6 = get_no_extract () in
             let uu___7 = get_extract_namespace () in
             let uu___8 = get_extract_module () in (uu___6, uu___7, uu___8) in
           match uu___5 with
           | ([], [], []) -> ()
           | uu___6 ->
               FStarC_Effect.failwith
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
               FStarC_Util.for_some
                 (fun n ->
                    FStarC_Util.starts_with m2 (FStarC_String.lowercase n))
                 ns in
         let should_extract_module m2 =
           let uu___4 = get_extract_module () in
           match uu___4 with
           | [] -> false
           | l ->
               FStarC_Util.for_some
                 (fun n -> (FStarC_String.lowercase n) = m2) l in
         let uu___4 = let uu___5 = no_extract m1 in Prims.op_Negation uu___5 in
         if uu___4
         then
           let uu___5 =
             let uu___6 = get_extract_namespace () in
             let uu___7 = get_extract_module () in (uu___6, uu___7) in
           (match uu___5 with
            | ([], []) -> if tgt = Krml then true else should_check m1
            | uu___6 ->
                let uu___7 = should_extract_namespace m1 in
                if uu___7 then true else should_extract_module m1)
         else false)
let should_be_already_cached (m : Prims.string) : Prims.bool=
  let uu___ = let uu___3 = should_check m in Prims.op_Negation uu___3 in
  if uu___
  then
    let uu___3 = get_already_cached () in
    match uu___3 with
    | FStar_Pervasives_Native.None -> false
    | FStar_Pervasives_Native.Some already_cached_setting ->
        module_matches_namespace_filter m already_cached_setting
  else false
let profile_enabled (modul_opt : Prims.string FStar_Pervasives_Native.option)
  (phase : Prims.string) : Prims.bool=
  match modul_opt with
  | FStar_Pervasives_Native.None ->
      let uu___ = get_profile_component () in
      matches_namespace_filter_opt phase uu___
  | FStar_Pervasives_Native.Some modul ->
      let uu___ =
        let uu___3 =
          let uu___4 = get_profile () in
          matches_namespace_filter_opt modul uu___4 in
        if uu___3
        then
          let uu___4 = get_profile_component () in
          matches_namespace_filter_opt phase uu___4
        else false in
      if uu___
      then true
      else
        (let uu___3 =
           let uu___4 = timing () in
           if uu___4
           then phase = "FStarC.TypeChecker.Tc.process_one_decl"
           else false in
         if uu___3 then should_check modul else false)
exception File_argument of Prims.string 
let uu___is_File_argument (projectee : Prims.exn) : Prims.bool=
  match projectee with | File_argument uu___ -> true | uu___ -> false
let __proj__File_argument__item__uu___ (projectee : Prims.exn) :
  Prims.string= match projectee with | File_argument uu___ -> uu___
let set_options (s : Prims.string) : FStarC_Getopt.parse_cmdline_res=
  try
    (fun uu___ ->
       match () with
       | () ->
           if s = ""
           then FStarC_Getopt.Success
           else
             (let settable_specs1 =
                FStarC_List.map FStar_Pervasives_Native.fst settable_specs in
              let res =
                FStarC_Getopt.parse_string settable_specs1
                  (fun s1 ->
                     FStarC_Effect.raise (File_argument s1);
                     FStarC_Getopt.Error
                       ("set_options with file argument", "")) s in
              if res = FStarC_Getopt.Success then set_error_flags () else res))
      ()
  with
  | File_argument s1 ->
      FStarC_Getopt.Error
        ((FStarC_Format.fmt1 "File %s is not a valid option" s1), "")
let with_options (s : Prims.string) (f : unit -> 'a) : 'a=
  with_saved_options (fun uu___ -> (let uu___4 = set_options s in ()); f ())
let get_vconfig (uu___ : unit) : FStarC_VConfig.vconfig=
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
let set_vconfig (vcfg : FStarC_VConfig.vconfig) : unit=
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
       FStarC_List.map (fun uu___24 -> String uu___24)
         vcfg.FStarC_VConfig.z3cliopt in
     List uu___23 in
   set_option "z3cliopt" uu___22);
  (let uu___23 =
     let uu___24 =
       FStarC_List.map (fun uu___25 -> String uu___25)
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
  set_option "reuse_hint_for"
    (option_as (fun uu___30 -> String uu___30)
       vcfg.FStarC_VConfig.reuse_hint_for)
let showable_codegen_t : codegen_t FStarC_Class_Show.showable=
  { FStarC_Class_Show.show = print_codegen }

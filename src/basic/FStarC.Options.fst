(*
   Copyright 2008-2020 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module FStarC.Options

open FStar open FStarC
open FStarC.BaseTypes
open FStarC
open FStarC.Effect
open FStarC.List
open FStarC.String
open FStarC.Util
open FStarC.Getopt
open FStar.Pervasives
open FStarC.VConfig
open FStarC.Class.Show
open FStarC.Class.Deq

module Option = FStarC.Option
module FC = FStarC.Common
module Util = FStarC.Util
module List = FStarC.List

module Ext = FStarC.Options.Ext

let debug_embedding = mk_ref false
let eager_embedding = mk_ref false

(* A FLAG TO INDICATE THAT WE'RE RUNNING UNIT TESTS *)
let __unit_tests__ = Util.mk_ref false
let __unit_tests() = !__unit_tests__
let __set_unit_tests () = __unit_tests__ := true
let __clear_unit_tests () = __unit_tests__ := false

let as_bool = function
  | Bool b -> b
  | _ -> failwith "Impos: expected Bool"
let as_int = function
  | Int b -> b
  | _ -> failwith "Impos: expected Int"
let as_string = function
  | String b -> b
  | Path b -> b
  | _ -> failwith "Impos: expected String"
let as_list' = function
  | List ts -> ts
  | _ -> failwith "Impos: expected List"
let as_list as_t x =
  as_list' x |> List.map as_t
let as_option as_t = function
  | Unset -> None
  | v -> Some (as_t v)
let as_comma_string_list = function
  | List ls -> List.flatten <| List.map (fun l -> split (as_string l) ",") ls
  | _ -> failwith "Impos: expected String (comma list)"

let copy_optionstate m = Util.smap_copy m

(* The option state is a stack of stacks. Why? First, we need to
 * support #push-options and #pop-options, which provide the user with
 * a stack-like option control, useful for rlimits and whatnot. Second,
 * there's the interactive mode, which allows to traverse a file and
 * backtrack over it, and must update this state accordingly. So for
 * instance consider the following code:
 *
 *   1. #push-options "A"
 *   2. let f = ...
 *   3. #pop-options
 *
 * Running in batch mode starts with a singleton stack, then pushes,
 * then pops. In the interactive mode, say we go over line 1. Then
 * our current state is a stack with two elements (original state and
 * state+"A"), but we need the previous state too to backtrack if we run
 * C-c C-p or whatever. We can also go over line 3, and still we need
 * to keep track of everything to backtrack. After processing the lines
 * one-by-one in the interactive mode, the stacks are: (top at the head)
 *
 *      (orig)
 *      (orig + A) (orig)
 *      (orig)
 *
 * No stack should ever be empty! Any of these failwiths should never be
 * triggered externally. IOW, the API should protect this invariant.
 *
 * We also keep a snapshot of the Debug module's state.
 *)
let history1 = Debug.saved_state & Ext.ext_state & optionstate

let fstar_options : ref optionstate = Util.mk_ref (Util.psmap_empty ())

let history : ref (list (list history1)) =
  Util.mk_ref [] // IRRELEVANT: see clear() below

let peek () = !fstar_options

let internal_push () =
  let lev1::rest = !history in
  let newhd = (Debug.snapshot (), Ext.save (), !fstar_options) in
  history := (newhd :: lev1) :: rest

let internal_pop () =
  let lev1::rest = !history in
  match lev1 with
  | [] -> false
  | (dbg, ext, opts)::lev1' ->
    Debug.restore dbg;
    Ext.restore ext;
    fstar_options := opts;
    history := lev1' :: rest;
    true

let push () = // already signal-atomic
  (* This turns a stack like

        4
        3
        2 1      current:5
  into:
        5
      4 4
      3 3
      2 2 1      current:5

  i.e.  current state does not change, and
  current minor stack does not change. The
  "next" previous stack (now with 2,3,4,5)
  has a copy of 5 at the top so we can restore regardless
  of what we do in the current stack or the current state. *)

  internal_push ();
  let lev1::_ = !history in
  history := lev1 :: !history;
  ignore (internal_pop());
  ()

let pop () = // already signal-atomic
  match !history with
  | [] -> failwith "TOO MANY POPS!"
  | _::levs ->
    history := levs;
    if not (internal_pop ()) then
      failwith "aaa!!!"

let set o =
  fstar_options := o

let depth () =
  let lev::_ = !history in
  List.length lev

let snapshot ()    = Common.snapshot push history ()
let rollback depth = Common.rollback pop  history depth

let set_option k v =
  let map : optionstate = peek() in
  if k = "report_assumes"
  then match Util.psmap_try_find map k with
       | Some (String "error") ->
         //It's already set to error; ignore any attempt to change it
         ()
       | _ -> fstar_options := Util.psmap_add map k v
  else fstar_options := Util.psmap_add map k v

let set_option' (k,v) =  set_option k v
let set_admit_smt_queries (b:bool) = set_option "admit_smt_queries" (Bool b)

let defaults =
     [
      ("abort_on"                     , Int 0);
      ("admit_smt_queries"            , Bool false);
      ("admit_except"                 , Unset);
      ("disallow_unification_guards"  , Bool false);
      ("already_cached"               , Unset);
      ("cache_checked_modules"        , Bool false);
      ("cache_dir"                    , Unset);
      ("cache_off"                    , Bool false);
      ("compat_pre_core"              , Unset);
      ("compat_pre_typed_indexed_effects"
                                      , Bool false);
      ("print_cache_version"          , Bool false);
      ("cmi"                          , Bool false);
      ("codegen"                      , Unset);
      ("codegen-lib"                  , List []);
      ("defensive"                    , String "no");
      ("debug"                        , List []);
      ("debug_all"                    , Bool false);
      ("debug_all_modules"            , Bool false);
      ("dep"                          , Unset);
      ("detail_errors"                , Bool false);
      ("detail_hint_replay"           , Bool false);
      ("dump_module"                  , List []);
      ("eager_subtyping"              , Bool false);
      ("error_contexts"               , Bool false);
      ("expose_interfaces"            , Bool false);
      ("message_format"               , String "auto");
      ("ext"                          , Unset);
      ("extract"                      , Unset);
      ("extract_all"                  , Bool false);
      ("extract_module"               , List []);
      ("extract_namespace"            , List []);
      ("full_context_dependency"      , Bool true);
      ("hide_uvar_nums"               , Bool false);
      ("hint_hook"                    , Unset);
      ("hint_info"                    , Bool false);
      ("hint_dir"                     , Unset);
      ("hint_file"                    , Unset);
      ("in"                           , Bool false);
      ("ide"                          , Bool false);
      ("ide_id_info_off"              , Bool false);
      ("lsp"                          , Bool false);
      ("include"                      , List []);
      ("print"                        , Bool false);
      ("print_in_place"               , Bool false);
      ("force"                        , Bool false);
      ("fuel"                         , Unset);
      ("ifuel"                        , Unset);
      ("initial_fuel"                 , Int 2);
      ("initial_ifuel"                , Int 1);
      ("keep_query_captions"          , Bool true);
      ("lax"                          , Bool false);
      ("load"                         , List []);
      ("load_cmxs"                    , List []);
      ("log_queries"                  , Bool false);
      ("log_failing_queries"          , Bool false);
      ("log_types"                    , Bool false);
      ("max_fuel"                     , Int 8);
      ("max_ifuel"                    , Int 2);
      ("MLish"                        , Bool false);
      ("MLish_effect"                 , String "FStar.Effect");
      ("no_default_includes"          , Bool false);
      ("no_extract"                   , List []);
      ("no_location_info"             , Bool false);
      ("no_smt"                       , Bool false);
      ("no_plugins"                   , Bool false);
      ("no_tactics"                   , Bool false);
      ("normalize_pure_terms_for_extraction"
                                      , Bool false);
      ("krmloutput"                   , Unset);
      ("odir"                         , Unset);
      ("output_deps_to"               , Unset);
      ("prims"                        , Unset);
      ("pretype"                      , Bool true);
      ("prims_ref"                    , Unset);
      ("print_bound_var_types"        , Bool false);
      ("print_effect_args"            , Bool false);
      ("print_expected_failures"      , Bool false);
      ("print_full_names"             , Bool false);
      ("print_implicits"              , Bool false);
      ("print_universes"              , Bool false);
      ("print_z3_statistics"          , Bool false);
      ("prn"                          , Bool false);
      ("proof_recovery"               , Bool false);
      ("quake"                        , Int 0);
      ("quake_lo"                     , Int 1);
      ("quake_hi"                     , Int 1);
      ("quake_keep"                   , Bool false);
      ("query_cache"                  , Bool false);
      ("query_stats"                  , Bool false);
      ("read_checked_file"            , Unset);
      ("list_plugins"                 , Bool false);
      ("locate"                       , Bool false);
      ("locate_lib"                   , Bool false);
      ("locate_ocaml"                 , Bool false);
      ("locate_file"                  , Unset);
      ("locate_z3"                    , Unset);
      ("read_krml_file"               , Unset);
      ("record_hints"                 , Bool false);
      ("record_options"               , Bool false);
      ("report_assumes"               , Unset);
      ("retry"                        , Bool false);
      ("reuse_hint_for"               , Unset);
      ("silent"                       , Bool false);
      ("smt"                          , Unset);
      ("smtencoding.elim_box"         , Bool false);
      ("smtencoding.nl_arith_repr"    , String "boxwrap");
      ("smtencoding.l_arith_repr"     , String "boxwrap");
      ("smtencoding.valid_intro"      , Bool true);
      ("smtencoding.valid_elim"       , Bool false);
      ("split_queries"                , String "on_failure");
      ("tactics_failhard"             , Bool false);
      ("tactics_info"                 , Bool false);
      ("tactic_raw_binders"           , Bool false);
      ("tactic_trace"                 , Bool false);
      ("tactic_trace_d"               , Int 0);

      ("tcnorm"                       , Bool true);
      ("timing"                       , Bool false);
      ("trace_error"                  , Bool false);
      ("ugly"                         , Bool false);
      ("unthrottle_inductives"        , Bool false);
      ("unsafe_tactic_exec"           , Bool false);
      ("use_native_tactics"           , Unset);
      ("use_eq_at_higher_order"       , Bool false);
      ("use_hints"                    , Bool false);
      ("use_hint_hashes"              , Bool false);
      ("using_facts_from"             , Unset);
      ("verify_module"                , List []);
      ("warn_default_effects"         , Bool false);
      ("z3refresh"                    , Bool false);
      ("z3rlimit"                     , Int 5);
      ("z3rlimit_factor"              , Int 1);
      ("z3seed"                       , Int 0);
      ("z3cliopt"                     , List []);
      ("z3smtopt"                     , List []);
      ("z3version"                    , String "4.8.5");
      ("__no_positivity"              , Bool false);
      ("__tactics_nbe"                , Bool false);
      ("warn_error"                   , List []);
      ("use_nbe"                      , Bool false);
      ("use_nbe_for_extraction"       , Bool false);
      ("trivial_pre_for_unannotated_effectful_fns"
                                      , Bool true);
      ("with_fstarc"                  , Bool false);
      ("profile_group_by_decl"        , Bool false);
      ("profile_component"            , Unset);
      ("profile"                      , Unset);
      ]

let init () =
  Debug.disable_all ();
  Ext.reset ();
  fstar_options := Util.psmap_empty ();
  defaults |> List.iter set_option'                          //initialize it with the default values

let clear () =
  history := [[]];
  init()

(* Run it now. *)
let _ = clear ()

let get_option s =
  match Util.psmap_try_find (peek ()) s with
  | None -> failwith ("Impossible: option " ^s^ " not found")
  | Some s -> s

let rec option_val_to_string (v:option_val) : string =
  match v with
  | Bool b -> "Bool " ^ show b
  | String s -> "String " ^ show s
  | Path s -> "Path " ^ show s
  | Int i -> "Int " ^ show i
  | List vs -> "List " ^ Common.string_of_list option_val_to_string vs
  | Unset -> "Unset"

instance showable_option_val : showable option_val = {
  show = option_val_to_string;
}

let rec eq_option_val (v1 v2 : option_val) : bool =
  match v1, v2 with
  | Bool x1, Bool x2
  | String x1, String x2
  | Path x1, Path x2
  | Int x1, Int x2 -> x1 =? x2
  | Unset, Unset -> true
  | List x1, List x2 ->
    Common.eq_list eq_option_val x1 x2
  | _, _ -> false

instance deq_option_val : deq option_val = {
  (=?) = eq_option_val;
}

let rec list_try_find #a #b {| deq a |} (k : a) (l : list (a & b))
: option b
=
  match l with
  | [] -> None
  | (k', v') :: l' ->
    if k =? k'
    then Some v'
    else list_try_find k l'

let show_options () =
  let s = peek () in
  let kvs : list (string & option_val) =
    let open FStarC.Class.Monad in
    let! k = Common.psmap_keys s in
    (* verify_module is only set internally. *)
    if k = "verify_module" then [] else
    let v = must <| psmap_try_find s k in
    let v0 = list_try_find k defaults in
    if v0 =? Some v then
      []
    else
      return (k, v)
  in
  let rec show_optionval v =
    match v with
    | String s -> "\"" ^ s ^ "\"" // FIXME: proper escape
    | Bool b -> show b
    | Int i -> show i
    | Path s -> s
    | List s -> List.map show_optionval s |> String.concat ","
    | Unset -> "<unset>"
  in
  let show1 (k, v) =
    Util.format2 "--%s %s" k (show_optionval v)
  in
  kvs |> List.map show1 |> String.concat "\n"

let set_verification_options o =
  (* This are all the options restored when processing a check_with
     attribute. All others are unchanged. We do this for two reasons:
     1) It's unsafe to just set everything (e.g. verify_module would
        cause lax verification, so we need to filter some stuff out).
     2) So we don't propagate meaningless debugging options, which
        is probably not intended.
   *)
  let verifopts = [
    "initial_fuel";
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
    "trivial_pre_for_unannotated_effectful_fns";
  ] in
  List.iter (fun k -> set_option k (Util.psmap_try_find o k |> Util.must)) verifopts

let lookup_opt s c =
  c (get_option s)

let get_abort_on                ()      = lookup_opt "abort_on"                 as_int
let get_admit_smt_queries       ()      = lookup_opt "admit_smt_queries"        as_bool
let get_admit_except            ()      = lookup_opt "admit_except"             (as_option as_string)
let get_compat_pre_core         ()      = lookup_opt "compat_pre_core"          (as_option as_int)

let get_compat_pre_typed_indexed_effects ()  = lookup_opt "compat_pre_typed_indexed_effects" as_bool
let get_disallow_unification_guards  ()      = lookup_opt "disallow_unification_guards"      as_bool

let get_already_cached          ()      = lookup_opt "already_cached"           (as_option (as_list as_string))
let get_cache_checked_modules   ()      = lookup_opt "cache_checked_modules"    as_bool
let get_cache_dir               ()      = lookup_opt "cache_dir"                (as_option as_string)
let get_cache_off               ()      = lookup_opt "cache_off"                as_bool
let get_print_cache_version     ()      = lookup_opt "print_cache_version"      as_bool
let get_cmi                     ()      = lookup_opt "cmi"                      as_bool
let get_codegen                 ()      = lookup_opt "codegen"                  (as_option as_string)
let get_codegen_lib             ()      = lookup_opt "codegen-lib"              (as_list as_string)
let get_defensive               ()      = lookup_opt "defensive"                as_string
let get_dep                     ()      = lookup_opt "dep"                      (as_option as_string)
let get_detail_errors           ()      = lookup_opt "detail_errors"            as_bool
let get_detail_hint_replay      ()      = lookup_opt "detail_hint_replay"       as_bool
let get_dump_module             ()      = lookup_opt "dump_module"              (as_list as_string)
let get_eager_subtyping         ()      = lookup_opt "eager_subtyping"          as_bool
let get_error_contexts          ()      = lookup_opt "error_contexts"           as_bool
let get_expose_interfaces       ()      = lookup_opt "expose_interfaces"        as_bool
let get_message_format          ()      = lookup_opt "message_format"           as_string
let get_extract                 ()      = lookup_opt "extract"                  (as_option (as_list as_string))
let get_extract_module          ()      = lookup_opt "extract_module"           (as_list as_string)
let get_extract_namespace       ()      = lookup_opt "extract_namespace"        (as_list as_string)
let get_force                   ()      = lookup_opt "force"                    as_bool
let get_hide_uvar_nums          ()      = lookup_opt "hide_uvar_nums"           as_bool
let get_hint_info               ()      = lookup_opt "hint_info"                as_bool
let get_hint_dir                ()      = lookup_opt "hint_dir"                 (as_option as_string)
let get_hint_file               ()      = lookup_opt "hint_file"                (as_option as_string)
let get_in                      ()      = lookup_opt "in"                       as_bool
let get_ide                     ()      = lookup_opt "ide"                      as_bool
let get_ide_id_info_off         ()      = lookup_opt "ide_id_info_off"          as_bool
let get_lsp                     ()      = lookup_opt "lsp"                      as_bool
let get_include                 ()      = lookup_opt "include"                  (as_list as_string)
let get_print                   ()      = lookup_opt "print"                    as_bool
let get_print_in_place          ()      = lookup_opt "print_in_place"           as_bool
let get_initial_fuel            ()      = lookup_opt "initial_fuel"             as_int
let get_initial_ifuel           ()      = lookup_opt "initial_ifuel"            as_int
let get_keep_query_captions     ()      = lookup_opt "keep_query_captions"      as_bool
let get_lax                     ()      = lookup_opt "lax"                      as_bool
let get_load                    ()      = lookup_opt "load"                     (as_list as_string)
let get_load_cmxs               ()      = lookup_opt "load_cmxs"                (as_list as_string)
let get_log_queries             ()      = lookup_opt "log_queries"              as_bool
let get_log_failing_queries     ()      = lookup_opt "log_failing_queries"      as_bool
let get_log_types               ()      = lookup_opt "log_types"                as_bool
let get_max_fuel                ()      = lookup_opt "max_fuel"                 as_int
let get_max_ifuel               ()      = lookup_opt "max_ifuel"                as_int
let get_MLish                   ()      = lookup_opt "MLish"                    as_bool
let get_MLish_effect            ()      = lookup_opt "MLish_effect"             as_string
let get_no_default_includes     ()      = lookup_opt "no_default_includes"      as_bool
let get_no_extract              ()      = lookup_opt "no_extract"               (as_list as_string)
let get_no_location_info        ()      = lookup_opt "no_location_info"         as_bool
let get_no_plugins              ()      = lookup_opt "no_plugins"               as_bool
let get_no_smt                  ()      = lookup_opt "no_smt"                   as_bool
let get_normalize_pure_terms_for_extraction
                                ()      = lookup_opt "normalize_pure_terms_for_extraction" as_bool
let get_krmloutput              ()      = lookup_opt "krmloutput"               (as_option as_string)
let get_odir                    ()      = lookup_opt "odir"                     (as_option as_string)
let get_output_deps_to          ()      = lookup_opt "output_deps_to"           (as_option as_string)
let get_ugly                    ()      = lookup_opt "ugly"                     as_bool
let get_prims                   ()      = lookup_opt "prims"                    (as_option as_string)
let get_print_bound_var_types   ()      = lookup_opt "print_bound_var_types"    as_bool
let get_print_effect_args       ()      = lookup_opt "print_effect_args"        as_bool
let get_print_expected_failures ()      = lookup_opt "print_expected_failures"  as_bool
let get_print_full_names        ()      = lookup_opt "print_full_names"         as_bool
let get_print_implicits         ()      = lookup_opt "print_implicits"          as_bool
let get_print_universes         ()      = lookup_opt "print_universes"          as_bool
let get_print_z3_statistics     ()      = lookup_opt "print_z3_statistics"      as_bool
let get_prn                     ()      = lookup_opt "prn"                      as_bool
let get_proof_recovery          ()      = lookup_opt "proof_recovery"           as_bool
let get_quake_lo                ()      = lookup_opt "quake_lo"                 as_int
let get_quake_hi                ()      = lookup_opt "quake_hi"                 as_int
let get_quake_keep              ()      = lookup_opt "quake_keep"               as_bool
let get_query_cache             ()      = lookup_opt "query_cache"              as_bool
let get_query_stats             ()      = lookup_opt "query_stats"              as_bool
let get_read_checked_file       ()      = lookup_opt "read_checked_file"        (as_option as_string)
let get_read_krml_file          ()      = lookup_opt "read_krml_file"           (as_option as_string)
let get_list_plugins            ()      = lookup_opt "list_plugins"             as_bool
let get_locate                  ()      = lookup_opt "locate"                   as_bool
let get_locate_lib              ()      = lookup_opt "locate_lib"               as_bool
let get_locate_ocaml            ()      = lookup_opt "locate_ocaml"             as_bool
let get_locate_file             ()      = lookup_opt "locate_file"              (as_option as_string)
let get_locate_z3               ()      = lookup_opt "locate_z3"                (as_option as_string)
let get_record_hints            ()      = lookup_opt "record_hints"             as_bool
let get_record_options          ()      = lookup_opt "record_options"           as_bool
let get_retry                   ()      = lookup_opt "retry"                    as_bool
let get_reuse_hint_for          ()      = lookup_opt "reuse_hint_for"           (as_option as_string)
let get_report_assumes          ()      = lookup_opt "report_assumes"           (as_option as_string)
let get_silent                  ()      = lookup_opt "silent"                   as_bool
let get_smt                     ()      = lookup_opt "smt"                      (as_option as_string)
let get_smtencoding_elim_box    ()      = lookup_opt "smtencoding.elim_box"     as_bool
let get_smtencoding_nl_arith_repr ()    = lookup_opt "smtencoding.nl_arith_repr" as_string
let get_smtencoding_l_arith_repr()      = lookup_opt "smtencoding.l_arith_repr" as_string
let get_smtencoding_valid_intro ()      = lookup_opt "smtencoding.valid_intro"  as_bool
let get_smtencoding_valid_elim  ()      = lookup_opt "smtencoding.valid_elim"   as_bool
let get_split_queries           ()      = lookup_opt "split_queries"            as_string
let get_tactic_raw_binders      ()      = lookup_opt "tactic_raw_binders"       as_bool
let get_tactics_failhard        ()      = lookup_opt "tactics_failhard"         as_bool
let get_tactics_info            ()      = lookup_opt "tactics_info"             as_bool
let get_tactic_trace            ()      = lookup_opt "tactic_trace"             as_bool
let get_tactic_trace_d          ()      = lookup_opt "tactic_trace_d"           as_int
let get_tactics_nbe             ()      = lookup_opt "__tactics_nbe"            as_bool
let get_tcnorm                  ()      = lookup_opt "tcnorm"                   as_bool
let get_timing                  ()      = lookup_opt "timing"                   as_bool
let get_trace_error             ()      = lookup_opt "trace_error"              as_bool
let get_unthrottle_inductives   ()      = lookup_opt "unthrottle_inductives"    as_bool
let get_unsafe_tactic_exec      ()      = lookup_opt "unsafe_tactic_exec"       as_bool
let get_use_eq_at_higher_order  ()      = lookup_opt "use_eq_at_higher_order"   as_bool
let get_use_hints               ()      = lookup_opt "use_hints"                as_bool
let get_use_hint_hashes         ()      = lookup_opt "use_hint_hashes"          as_bool
let get_use_native_tactics      ()      = lookup_opt "use_native_tactics"       (as_option as_string)
let get_no_tactics              ()      = lookup_opt "no_tactics"               as_bool
let get_using_facts_from        ()      = lookup_opt "using_facts_from"         (as_option (as_list as_string))
let get_verify_module           ()      = lookup_opt "verify_module"            (as_list as_string)
let get_version                 ()      = lookup_opt "version"                  as_bool
let get_warn_default_effects    ()      = lookup_opt "warn_default_effects"     as_bool
let get_z3cliopt                ()      = lookup_opt "z3cliopt"                 (as_list as_string)
let get_z3smtopt                ()      = lookup_opt "z3smtopt"                 (as_list as_string)
let get_z3refresh               ()      = lookup_opt "z3refresh"                as_bool
let get_z3rlimit                ()      = lookup_opt "z3rlimit"                 as_int
let get_z3rlimit_factor         ()      = lookup_opt "z3rlimit_factor"          as_int
let get_z3seed                  ()      = lookup_opt "z3seed"                   as_int
let get_z3version               ()      = lookup_opt "z3version"                as_string
let get_no_positivity           ()      = lookup_opt "__no_positivity"          as_bool
let get_warn_error              ()      = lookup_opt "warn_error"               (as_list as_string)
let get_use_nbe                 ()      = lookup_opt "use_nbe"                  as_bool
let get_use_nbe_for_extraction  ()      = lookup_opt "use_nbe_for_extraction"                  as_bool
let get_trivial_pre_for_unannotated_effectful_fns
                                ()      = lookup_opt "trivial_pre_for_unannotated_effectful_fns"    as_bool
let get_with_fstarc             ()      = lookup_opt "with_fstarc"                                  as_bool
let get_profile                 ()      = lookup_opt "profile"                  (as_option (as_list as_string))
let get_profile_group_by_decl   ()      = lookup_opt "profile_group_by_decl"    as_bool
let get_profile_component       ()      = lookup_opt "profile_component"        (as_option (as_list as_string))

// See comment in the interface file
let _version = Util.mk_ref ""
let _platform = Util.mk_ref ""
let _compiler = Util.mk_ref ""
let _date = Util.mk_ref " not set"
let _commit = Util.mk_ref ""

let display_version () =
  Util.print_string (Util.format5 "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n"
                                  !_version !_platform !_compiler !_date !_commit)

let bold_doc (d:Pprint.document) : Pprint.document =
  let open FStarC.Pprint in
  (* very hacky, this would make no sense for documents going elsewhere
  other than stdout *)
  if stdout_isatty () = Some true
  then fancystring "\x1b[39;1m" 0 ^^ d ^^ fancystring "\x1b[0m" 0
  else d

let display_debug_keys () =
  let keys = Debug.list_all_toggles () in
  keys |> List.sortWith String.compare |> List.iter (fun s -> Util.print_string (s ^ "\n"))

let usage_for (o : opt & Pprint.document) : Pprint.document =
  let open FStarC.Pprint in
  let open FStarC.Errors.Msg in
  let ((short, flag, p), explain) = o in
  let arg =
    match p with
    | ZeroArgs _ -> empty
    | OneArg (_, argname) -> blank 1 ^^ doc_of_string argname
  in
  let short_opt =
    if short <> noshort
    then [doc_of_string ("-" ^ String.make 1 short) ^^ arg]
    else []
  in
  let long_opt =
    if flag <> ""
    then [doc_of_string ("--" ^ flag) ^^ arg]
    else []
  in
  group (bold_doc (separate (comma ^^ blank 1) (short_opt @ long_opt))) ^^ hardline ^^
  group (blank 4 ^^ align explain) ^^ hardline

let display_usage_aux (specs : list (opt & Pprint.document)) : unit =
  let open FStarC.Pprint in
  let open FStarC.Errors.Msg in
  let text (s:string) : document = flow (break_ 1) (words s) in
  let d : document =
    doc_of_string "fstar.exe [options] file[s] [@respfile...]" ^/^
    doc_of_string (Util.format1 "  %srespfile: read command-line options from respfile\n" (Util.colorize_bold "@")) ^/^
    List.fold_right (fun o rest -> usage_for o ^^ rest) specs empty
  in
  Util.print_string (pretty_string (float_of_string "1.0") 80 d)

let mk_spec (o : char & string & opt_variant option_val) : opt =
    let ns, name, arg = o in
    let arg =
        match arg with
        | ZeroArgs f ->
          let g () = set_option name (f()) in
          ZeroArgs g

        | OneArg (f, d) ->
          let g x = set_option name (f x) in
          OneArg (g, d) in
    ns, name, arg

let accumulated_option name value =
    let prev_values = Util.dflt [] (lookup_opt name (as_option as_list')) in
    List (value :: prev_values)

let reverse_accumulated_option name value =
    let prev_values = Util.dflt [] (lookup_opt name (as_option as_list')) in
    List (prev_values @ [value])

let accumulate_string name post_processor value =
    set_option name (accumulated_option name (String (post_processor value)))

let add_extract_module s =
    accumulate_string "extract_module" String.lowercase s

let add_extract_namespace s =
    accumulate_string "extract_namespace" String.lowercase s

let add_verify_module s =
    accumulate_string "verify_module" String.lowercase s

exception InvalidArgument of string // option name

(** Parse option value `str_val` according to specification `typ`.

For example, to parse the value "OCaml" for the option "--codegen", this
function is called as ``parse_opt_val "codegen" (EnumStr ["OCaml"; "FSharp";
"krml"]) "OCaml"`` and returns ``String "OCaml"``.

`opt_name` is only used in error messages. **)
let rec parse_opt_val (opt_name: string) (typ: opt_type) (str_val: string) : option_val =
  try
    match typ with
    | Const c -> c
    | IntStr _ -> (match safe_int_of_string str_val with
                  | Some v -> Int v
                  | None -> raise (InvalidArgument opt_name))
    | BoolStr -> Bool (if str_val = "true" then true
                         else if str_val = "false" then false
                         else raise (InvalidArgument opt_name))
    | PathStr _ -> Path str_val
    | SimpleStr _ -> String str_val
    | EnumStr strs -> if List.mem str_val strs then String str_val
                     else raise (InvalidArgument opt_name)
    | OpenEnumStr _ -> String str_val
    | PostProcessed (pp, elem_spec) -> pp (parse_opt_val opt_name elem_spec str_val)
    | Accumulated elem_spec -> let v = parse_opt_val opt_name elem_spec str_val in
                              accumulated_option opt_name v
    | ReverseAccumulated elem_spec -> let v = parse_opt_val opt_name elem_spec str_val in
                                     reverse_accumulated_option opt_name v
    | WithSideEffect (side_effect, elem_spec) -> side_effect ();
                                                parse_opt_val opt_name elem_spec str_val
  with
  | InvalidArgument opt_name ->
    failwith (Util.format1 "Invalid argument to --%s" opt_name)

let rec desc_of_opt_type typ : option string =
  let desc_of_enum cases = Some (String.concat "|" cases) in
  match typ with
  | Const c -> None
  | IntStr desc -> Some desc
  | BoolStr -> desc_of_enum ["true"; "false"]
  | PathStr desc -> Some desc
  | SimpleStr desc -> Some desc
  | EnumStr strs -> desc_of_enum strs
  | OpenEnumStr (strs, desc) -> desc_of_enum (strs @ [desc])
  | PostProcessed (_, elem_spec)
  | Accumulated elem_spec
  | ReverseAccumulated elem_spec
  | WithSideEffect (_, elem_spec) -> desc_of_opt_type elem_spec

let arg_spec_of_opt_type opt_name typ : opt_variant option_val =
  let wrap s = "<" ^ s ^ ">" in
  let parser = parse_opt_val opt_name typ in
  match desc_of_opt_type typ with
  | None -> ZeroArgs (fun () -> parser "")
  | Some desc ->
    let desc = wrap desc in
    OneArg (parser, desc)

let pp_validate_dir p =
  let pp = as_string p in
  mkdir (*clean=*)false (*mkparents=*)true pp;
  p

let pp_lowercase s =
  String (String.lowercase (as_string s))

let abort_counter : ref int =
    mk_ref 0

let interp_quake_arg (s:string)
            : int & int & bool =
           (* min,  max,  keep_going *)
  let ios = int_of_string in
  match split s "/" with
  | [f] -> ios f, ios f, false
  | [f1; f2] ->
    if f2 = "k"
    then ios f1, ios f1, true
    else ios f1, ios f2, false
  | [f1; f2; k] ->
    if k = "k"
    then ios f1, ios f2, true
    else failwith "unexpected value for --quake"
  | _ -> failwith "unexpected value for --quake"

let set_option_warning_callback_aux,
    option_warning_callback =
    let cb = mk_ref None in
    let set (f:string -> unit) =
      cb := Some f
    in
    let call msg =
      match !cb with
      | None -> ()
      | Some f -> f msg
    in
    set, call
let set_option_warning_callback f = set_option_warning_callback_aux f

let rec specs_with_types warn_unsafe : list (char & string & opt_type & Pprint.document) =
  let open FStarC.Pprint in
  let open FStarC.Errors.Msg in
  let text (s:string) : document = flow (break_ 1) (words s) in
  [
  ( noshort, "abort_on",
    PostProcessed ((function Int x -> abort_counter := x; Int x
                           | x -> failwith "?"), IntStr "non-negative integer"),
    text "Abort on the n-th error or warning raised. Useful in combination with --trace_error. Count starts at 1, use 0 to disable. (default 0)");

  ( noshort,
    "admit_smt_queries",
    WithSideEffect ((fun _ -> if warn_unsafe then option_warning_callback "admit_smt_queries"),
                   BoolStr),
    text "Admit SMT queries, unsafe! (default 'false')");

  ( noshort,
    "admit_except",
    WithSideEffect ((fun _ -> if warn_unsafe then option_warning_callback "admit_except"),
                    SimpleStr "[symbol|(symbol, id)]"),
    text "Admit all queries, except those with label ( symbol,  id))\
          (e.g. --admit_except '(FStar.Fin.pigeonhole, 1)' or --admit_except FStar.Fin.pigeonhole)");

  ( noshort,
    "compat_pre_core",
    IntStr "0, 1, 2",
    text "Retain behavior of the tactic engine prior to the introduction \
          of FStarC.TypeChecker.Core (0 is most permissive, 2 is least permissive)");

  ( noshort,
    "compat_pre_typed_indexed_effects",
    Const (Bool true),
    text "Retain untyped indexed effects implicits");

  ( noshort,
    "disallow_unification_guards",
    BoolStr,
    text "Fail if the SMT guard are produced when the tactic engine re-checks solutions produced by the unifier (default 'false')");

  ( noshort,
    "already_cached",
    Accumulated (SimpleStr "One or more space-separated occurrences of '[+|-]( * | namespace | module)'"),
    text "Expects all modules whose names or namespaces match the provided options \
          to already have valid .checked files in the include path");

  ( noshort,
    "cache_checked_modules",
    Const (Bool true),
    text "Write a '.checked' file for each module after verification and read from it if present, instead of re-verifying");

  ( noshort,
    "cache_dir",
    PostProcessed (pp_validate_dir, PathStr "dir"),
    text "Read and write .checked and .checked.lax in directory dir");

  ( noshort,
    "cache_off",
    Const (Bool true),
    text "Do not read or write any .checked files");

  ( noshort,
    "print_cache_version",
    Const (Bool true),
    text "Print the version for .checked files and exit.");

  ( noshort,
    "cmi",
    Const (Bool true),
    text "Inline across module interfaces during extraction (aka. cross-module inlining)");

  ( noshort,
    "codegen",
    EnumStr ["OCaml"; "FSharp"; "krml"; "Plugin"; "PluginNoLib"; "Extension"],
    text "Generate code for further compilation to executable code, or build a compiler plugin");

  ( noshort,
    "codegen-lib",
    Accumulated (SimpleStr "namespace"),
    text "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)");

  ( 'd',
    "",
    PostProcessed (
      (fun o ->
        Debug.enable ();
        o), Const (Bool true)),
    text "Enable general debugging, i.e. increase verbosity.");

  ( noshort,
    "debug",
    PostProcessed (
      (fun o ->
        let keys = as_comma_string_list o in
        Debug.enable_toggles keys;
        o), ReverseAccumulated (SimpleStr "debug toggles")),
    text "Enable specific debug toggles (comma-separated list of debug keys)");

  ( noshort,
    "debug_all",
    PostProcessed (
      (fun o ->
        match o with
        | Bool true ->
          Debug.set_debug_all ();
          o
        | _ -> failwith "?"
        ), Const (Bool true)),
    text "Enable all debug toggles. WARNING: this will cause a lot of output!");

  ( noshort,
    "debug_all_modules",
    Const (Bool true),
    text "Enable to make the effect of --debug apply to every module processed by the compiler, \
          including dependencies.");

  ( noshort,
    "defensive",
    EnumStr ["no"; "warn"; "error"; "abort"],
    text "Enable several internal sanity checks, useful to track bugs and report issues."
    ^^ bulleted [
         text "if 'no', no checks are performed";
         text "if 'warn', checks are performed and raise a warning when they fail";
         text "if 'error, like 'warn', but the compiler raises a hard error instead";
         text "if 'abort, like 'warn', but the compiler immediately aborts on an error"
       ]
    ^/^ text "(default 'no')");

  ( noshort,
    "dep",
    EnumStr ["make"; "graph"; "full"; "raw"],
    text "Output the transitive closure of the full dependency graph in three formats:"
    ^^ bulleted [
         text "'graph': a format suitable the 'dot' tool from 'GraphViz'";
         text "'full': a format suitable for 'make', including dependences for producing .ml and .krml files";
         text "'make': (deprecated) a format suitable for 'make', including only dependences among source files";
       ]);

  ( noshort,
    "detail_errors",
    Const (Bool true),
    text "Emit a detailed error report by asking the SMT solver many queries; will take longer");

  ( noshort,
   "detail_hint_replay",
    Const (Bool true),
    text "Emit a detailed report for proof whose unsat core fails to replay");

  ( noshort,
    "dump_module",
    Accumulated (SimpleStr "module_name"),
    text "Print out this module as it passes through the compiler pipeline");

  ( noshort,
    "eager_subtyping",
    Const (Bool true),
    text "Try to solve subtyping constraints at each binder (loses precision but may be slightly more efficient)");

  ( noshort,
    "error_contexts",
    BoolStr,
    text "Print context information for each error or warning raised (default false)");

  ( noshort,
    "ext",
    PostProcessed (
      (fun o ->
        let parse_ext (s:string) : list (string & string) =
          let exts = Util.split s ";" in
          List.collect (fun s ->
            match Util.split s "=" with
            | [k;v] -> [(k,v)]
            | _ -> [s, "1"]) exts
        in
        as_comma_string_list o |> List.collect parse_ext |> List.iter (fun (k, v) -> Ext.set k v);
        o), ReverseAccumulated (SimpleStr "extension knobs")),
    text "These options are set in extensions option map. Keys are usually namespaces separated by \":\". \
          E.g., 'pulse:verbose=1;my:extension:option=xyz;foo:bar=baz'. \
          These options are typically interpreted by extensions. \
          Any later use of --ext over the same key overrides the old value. \
          An entry 'e' that is not of the form 'a=b' is treated as 'e=1', i.e., 'e' associated with string \"1\".");

  ( noshort,
    "extract",
    Accumulated (SimpleStr "One or more semicolon separated occurrences of '[TargetName:]ModuleSelector'"),
    text "Extract only those modules whose names or namespaces match the provided options. \
     'TargetName' ranges over {OCaml, krml, FSharp, Plugin, PluginNoLib, Extension}. \
     A 'ModuleSelector' is a space or comma-separated list of '[+|-]( * | namespace | module)'. \
     For example --extract 'OCaml:A -A.B' --extract 'krml:A -A.C' --extract '*' means \
     for OCaml, extract everything in the A namespace only except A.B; \
     for krml, extract everything in the A namespace only except A.C; \
     for everything else, extract everything. \
     Note, the '+' is optional: --extract '+A' and --extract 'A' mean the same thing. \
     Note also that '--extract A' applies both to a module named 'A' and to any module in the 'A' namespace \
     Multiple uses of this option accumulate, e.g., --extract A --extract B is interpreted as --extract 'A B'.");

  ( noshort,
    "extract_module",
    Accumulated (PostProcessed (pp_lowercase, (SimpleStr "module_name"))),
    text "Deprecated: use --extract instead; Only extract the specified modules (instead of the possibly-partial dependency graph)");

  ( noshort,
    "extract_namespace",
    Accumulated (PostProcessed (pp_lowercase, (SimpleStr "namespace name"))),
    text "Deprecated: use --extract instead; Only extract modules in the specified namespace");

  ( noshort,
    "expose_interfaces",
    Const (Bool true),
    text "Explicitly break the abstraction imposed by the interface of any implementation file that appears on the command line (use with care!)");

  ( noshort,
    "message_format",
    EnumStr ["human"; "json"; "github"; "auto"],
    text "Format of the messages emitted by F*. Using 'auto' will use human messages \
          unless the variable GITHUB_ACTIONS is non-empty, in which case 'github' is \
          used (default `auto`).");

  ( noshort,
    "hide_uvar_nums",
    Const (Bool true),
    text "Don't print unification variable numbers");

  ( noshort,
    "hint_dir",
    PostProcessed (pp_validate_dir, PathStr "dir"),
    text "Read/write hints to  dir/module_name.hints (instead of placing hint-file alongside source file)");

  ( noshort,
    "hint_file",
    PathStr "path",
    text "Read/write hints to  path (instead of module-specific hints files; overrides hint_dir)");

  ( noshort,
    "hint_info",
    Const (Bool true),
    text "Print information regarding hints (deprecated; use --query_stats instead)");

  ( noshort,
    "in",
    Const (Bool true),
    text "Legacy interactive mode; reads input from stdin");

  ( noshort,
    "ide",
    Const (Bool true),
    text "JSON-based interactive mode for IDEs");

  ( noshort,
    "ide_id_info_off",
    Const (Bool true),
    text "Disable identifier tables in IDE mode (temporary workaround useful in Steel)");

  ( noshort,
    "lsp",
    Const (Bool true),
    text "Language Server Protocol-based interactive mode for IDEs");

  ( noshort,
    "include",
    ReverseAccumulated (PathStr "path"),
    text "A directory in which to search for files included on the command line");

  ( noshort,
    "print",
    Const (Bool true),
    text "Parses and prettyprints the files included on the command line");

  ( noshort,
    "print_in_place",
    Const (Bool true),
    text "Parses and prettyprints in place the files included on the command line");

  ( 'f',
    "force",
    Const (Bool true),
    text "Force checking the files given as arguments even if they have valid checked files");

  ( noshort,
    "fuel",
    PostProcessed
        ((function | String s ->
                     let p f = Int (int_of_string f) in
                     let min, max =
                       match Util.split s "," with
                       | [f] -> f, f
                       | [f1;f2] -> f1, f2
                       | _ -> failwith "unexpected value for --fuel"
                     in
                     set_option "initial_fuel" (p min);
                     set_option "max_fuel" (p max);
                     String s
                   | _ -> failwith "impos"),
        SimpleStr "non-negative integer or pair of non-negative integers"),
    text "Set initial_fuel and max_fuel at once");

  ( noshort,
    "ifuel",
    PostProcessed
        ((function | String s ->
                     let p f = Int (int_of_string f) in
                     let min, max =
                       match Util.split s "," with
                       | [f] -> f, f
                       | [f1;f2] -> f1, f2
                       | _ -> failwith "unexpected value for --ifuel"
                     in
                     set_option "initial_ifuel" (p min);
                     set_option "max_ifuel" (p max);
                     String s
                   | _ -> failwith "impos"),
        SimpleStr "non-negative integer or pair of non-negative integers"),
    text "Set initial_ifuel and max_ifuel at once");

  ( noshort,
    "initial_fuel",
    IntStr "non-negative integer",
    text "Number of unrolling of recursive functions to try initially (default 2)");

  ( noshort,
    "initial_ifuel",
    IntStr "non-negative integer",
    text "Number of unrolling of inductive datatypes to try at first (default 1)");

  ( noshort,
    "keep_query_captions",
    BoolStr,
    text "Retain comments in the logged SMT queries (requires --log_queries or --log_failing_queries; default true)");

  ( noshort,
    "lax",
    WithSideEffect ((fun () -> if warn_unsafe then option_warning_callback "lax"), Const (Bool true)),
    text "Run the lax-type checker only (admit all verification conditions)");

  ( noshort,
   "load",
    ReverseAccumulated (PathStr "module"),
    text "Load OCaml module, compiling it if necessary");

  ( noshort,
   "load_cmxs",
    ReverseAccumulated (PathStr "module"),
    text "Load compiled module, fails hard if the module is not already compiled");

  ( noshort,
    "log_types",
    Const (Bool true),
    text "Print types computed for data/val/let-bindings");

  ( noshort,
    "log_queries",
    Const (Bool true),
    text "Log the Z3 queries in several queries-*.smt2 files, as we go");

  ( noshort,
    "log_failing_queries",
    Const (Bool true),
    text "As --log_queries, but only save the failing queries. Each query is
    saved in its own file regardless of whether they were checked during the
    same invocation. The SMT2 file names begin with \"failedQueries\"");

  ( noshort,
    "max_fuel",
    IntStr "non-negative integer",
    text "Number of unrolling of recursive functions to try at most (default 8)");

  ( noshort,
    "max_ifuel",
    IntStr "non-negative integer",
    text "Number of unrolling of inductive datatypes to try at most (default 2)");

  ( noshort,
    "MLish",
    Const (Bool true),
    text "Trigger various specializations for compiling the F* compiler itself (not meant for user code)");

  ( noshort,
    "MLish_effect",
    SimpleStr "module_name",
    text "Set the default effect *module* for --MLish (default: FStar.Effect)");

  ( noshort,
    "no_default_includes",
    Const (Bool true),
    text "Ignore the default module search paths");

  ( noshort,
    "no_extract",
    Accumulated (PathStr "module name"),
    text "Deprecated: use --extract instead; Do not extract code from this module");

  ( noshort,
    "no_location_info",
    Const (Bool true),
    text "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)");

  ( noshort,
    "no_smt",
    Const (Bool true),
    text "Do not send any queries to the SMT solver, and fail on them instead");

  ( noshort,
    "normalize_pure_terms_for_extraction",
    Const (Bool true),
    text "Extract top-level pure terms after normalizing them. This can lead to very large code, but can result in more partial evaluation and compile-time specialization.");

  ( noshort,
    "krmloutput",
    PathStr "filename",
    text "Place KaRaMeL extraction output in file <filename>. The path can be relative or absolute and does not depend\
    on the --odir option.");

  ( noshort,
    "odir",
    PostProcessed (pp_validate_dir, PathStr "dir"),
    text "Place output in directory  dir");

  ( noshort,
    "output_deps_to",
    PathStr "file",
    text "Output the result of --dep into this file instead of to standard output.");

  ( noshort,
    "prims",
    PathStr "file",
    text "Use a custom Prims.fst file. Do not use if you do not know exactly what you're doing.");

  ( noshort,
    "print_bound_var_types",
    Const (Bool true),
    text "Print the types of bound variables");

  ( noshort,
    "print_effect_args",
    Const (Bool true),
    text "Print inferred predicate transformers for all computation types");

  ( noshort,
    "print_expected_failures",
    Const (Bool true),
    text "Print the errors generated by declarations marked with expect_failure, \
          useful for debugging error locations");

  ( noshort,
    "print_full_names",
    Const (Bool true),
    text "Print full names of variables");

  ( noshort,
    "print_implicits",
    Const (Bool true),
    text "Print implicit arguments");

  ( noshort,
    "print_universes",
    Const (Bool true),
    text "Print universes");

  ( noshort,
    "print_z3_statistics",
    Const (Bool true),
    text "Print Z3 statistics for each SMT query (details such as relevant modules, facts, etc. for each proof)");

  ( noshort,
    "prn",
    Const (Bool true),
    text "Print full names (deprecated; use --print_full_names instead)");

  ( noshort,
    "proof_recovery",
    Const (Bool true),
    text "Proof recovery mode: before failing an SMT query, retry 3 times, increasing rlimits. \
     If the query goes through after retrying, verification will succeed, but a warning will be emitted. \
     This feature is useful to restore a project after some change to its libraries or F* upgrade. \
     Importantly, then, this option cannot be used in a pragma (#set-options, etc).");

  ( noshort,
    "quake",
    PostProcessed
        ((function | String s ->
                     let min, max, k = interp_quake_arg s in
                     set_option "quake_lo" (Int min);
                     set_option "quake_hi" (Int max);
                     set_option "quake_keep" (Bool k);
                     set_option "retry" (Bool false);
                     String s
                   | _ -> failwith "impos"),
        SimpleStr "positive integer or pair of positive integers"),
    text "Repeats SMT queries to check for robustness" ^^
    bulleted [
      text "--quake N/M repeats each query checks that it succeeds at least N out of M times, aborting early if possible";
      text "--quake N/M/k works as above, except it will unconditionally run M times";
      text "--quake N is an alias for --quake N/N";
      text "--quake N/k is an alias for --quake N/N/k";
    ] ^^
    text "Using --quake disables --retry. When quake testing, queries are not splitted for error reporting unless \
          '--split_queries always' is given. Queries from the smt_sync tactic are not quake-tested.");

  ( noshort,
    "query_cache",
    Const (Bool true),
    text "Keep a running cache of SMT queries to make verification faster. \
          Only available in the interactive mode. \
          NOTE: This feature is experimental and potentially unsound! Hence why
          it is not allowed in batch mode (where it is also less useful). If you
          find a query that is mistakenly accepted with the cache, please
          report a bug to the F* issue tracker on GitHub.");

  ( noshort,
    "query_stats",
    Const (Bool true),
    text "Print SMT query statistics");

  ( noshort,
    "read_checked_file",
    PathStr "path",
    text "Read a checked file and dump it to standard output.");

  ( noshort,
    "read_krml_file",
    PathStr "path",
    text "Read a Karamel binary file and dump it to standard output.");

  ( noshort,
    "record_hints",
    Const (Bool true),
    text "Record a database of hints for efficient proof replay");

  ( noshort,
    "record_options",
    Const (Bool true),
    text "Record the state of options used to check each sigelt, useful \
          for the `check_with` attribute and metaprogramming. \
          Note that this implies a performance hit and increases the size of checked files.");

  ( noshort,
    "retry",
    PostProcessed
        ((function | Int i ->
                     set_option "quake_lo" (Int 1);
                     set_option "quake_hi" (Int i);
                     set_option "quake_keep" (Bool false);
                     set_option "retry" (Bool true);
                     Bool true
                   | _ -> failwith "impos"),
        IntStr "positive integer"),
    text "Retry each SMT query N times and succeed on the first try. Using --retry disables --quake.");

  ( noshort,
    "reuse_hint_for",
    SimpleStr "toplevel_name",
    text "Optimistically, attempt using the recorded hint for  toplevel_name (a top-level name in the current module) when trying to verify some other term 'g'");

  ( noshort,
    "report_assumes",
     EnumStr ["warn"; "error"],
    text "Report every use of an escape hatch, include assume, admit, etc.");

  ( noshort,
    "silent",
    Const (Bool true),
    text "Disable all non-critical output");

  ( noshort,
    "smt",
    PathStr "path",
    text "Path to the Z3 SMT solver (we could eventually support other solvers)");

  ( noshort,
    "smtencoding.elim_box",
    BoolStr,
    text "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')");

  ( noshort,
    "smtencoding.nl_arith_repr",
    EnumStr ["native"; "wrapped"; "boxwrap"],
    text "Control the representation of non-linear arithmetic functions in the SMT encoding:" ^^
    bulleted [
      text "if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'";
      text "if 'native' use '*, div, mod'";
      text "if 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'";
    ] ^^
    text "(default 'boxwrap')");

  ( noshort,
    "smtencoding.l_arith_repr",
    EnumStr ["native"; "boxwrap"],
    text "Toggle the representation of linear arithmetic functions in the SMT encoding:" ^^
    bulleted [
      text "if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'";
      text "if 'native', use '+, -, -'";
    ] ^^
    text "(default 'boxwrap')");

  ( noshort,
    "smtencoding.valid_intro",
    BoolStr,
    text "Include an axiom in the SMT encoding to introduce proof-irrelevance from a constructive proof");

  ( noshort,
    "smtencoding.valid_elim",
    BoolStr,
    text "Include an axiom in the SMT encoding to eliminate proof-irrelevance into the existence of a proof witness");

  ( noshort,
    "split_queries",
    EnumStr ["no"; "on_failure"; "always"],
    text "Split SMT verification conditions into several separate queries, one per goal. \
          Helps with localizing errors." ^^
    bulleted [
      text "Use 'no' to disable (this may reduce the quality of error messages).";
      text "Use 'on_failure' to split queries and retry when discharging fails (the default)";
      text "Use 'yes' to always split.";
    ]);

  ( noshort,
    "tactic_raw_binders",
    Const (Bool true),
    text "Do not use the lexical scope of tactics to improve binder names");

  ( noshort,
    "tactics_failhard",
    Const (Bool true),
    text "Do not recover from metaprogramming errors, and abort if one occurs");

  ( noshort,
    "tactics_info",
    Const (Bool true),
    text "Print some rough information on tactics, such as the time they take to run");

  ( noshort,
    "tactic_trace",
    Const (Bool true),
    text "Print a depth-indexed trace of tactic execution (Warning: very verbose)");

  ( noshort,
    "tactic_trace_d",
    IntStr "positive_integer",
    text "Trace tactics up to a certain binding depth");

  ( noshort,
    "__tactics_nbe",
    Const (Bool true),
    text "Use NBE to evaluate metaprograms (experimental)");

  ( noshort,
    "tcnorm",
    BoolStr,
    text "Attempt to normalize definitions marked as tcnorm (default 'true')");

  ( noshort,
    "timing",
    Const (Bool true),
    text "Print the time it takes to verify each top-level definition. \
          This is just an alias for an invocation of the profiler, so it may not work well if combined with --profile. \
          In particular, it implies --profile_group_by_decl.");

  ( noshort,
    "trace_error",
    Const (Bool true),
    text "Attach stack traces on errors");

  ( noshort,
    "ugly",
    Const (Bool true),
    text "Emit output formatted for debugging");

  ( noshort,
    "unthrottle_inductives",
    Const (Bool true),
    text "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)");

  ( noshort,
    "unsafe_tactic_exec",
    Const (Bool true),
    text "Allow tactics to run external processes. WARNING: checking an untrusted F* file while \
          using this option can have disastrous effects.");

  ( noshort,
    "use_eq_at_higher_order",
    Const (Bool true),
    text "Use equality constraints when comparing higher-order types (Temporary)");

  ( noshort,
    "use_hints",
    Const (Bool true),
    text "Use a previously recorded hints database for proof replay");

  ( noshort,
    "use_hint_hashes",
    Const (Bool true),
    text "Admit queries if their hash matches the hash recorded in the hints database");

  ( noshort,
     "use_native_tactics",
     PathStr "path",
    text "Use compiled tactics from  path");

  ( noshort,
    "no_plugins",
    Const (Bool true),
    text "Do not run plugins natively and interpret them as usual instead");

  ( noshort,
    "no_tactics",
    Const (Bool true),
    text "Do not run the tactic engine before discharging a VC");

  ( noshort,
    "using_facts_from",
    ReverseAccumulated (SimpleStr "One or more space-separated occurrences of '[+|-]( * | namespace | fact id)'"),
    text "Prunes the context to include only the facts from the given namespace or fact id. \
          Facts can be include or excluded using the [+|-] qualifier. \
          For example --using_facts_from '* -FStarC.Reflection +FStarC.List -FStarC.List.Tot' will \
          remove all facts from FStarC.List.Tot.*, \
          retain all remaining facts from FStarC.List.*, \
          remove all facts from FStarC.Reflection.*, \
          and retain all the rest. \
          Note, the '+' is optional: --using_facts_from 'FStarC.List' is equivalent to --using_facts_from '+FStarC.List'. \
          Multiple uses of this option accumulate, e.g., --using_facts_from A --using_facts_from B is interpreted as --using_facts_from A^B.");

  ( noshort,
    "__temp_fast_implicits",
    Const (Bool true),
    text "This does nothing and will be removed");

  ( 'v',
    "version",
    WithSideEffect ((fun _ -> display_version(); exit 0),
                    (Const (Bool true))),
    text "Display version number");

  ( noshort,
    "warn_default_effects",
    Const (Bool true),
    text "Warn when (a -> b) is desugared to (a -> Tot b)");

  ( noshort,
    "z3cliopt",
    ReverseAccumulated (SimpleStr "option"),
    text "Z3 command line options");

  ( noshort,
    "z3smtopt",
    ReverseAccumulated (SimpleStr "option"),
    text "Z3 options in smt2 format");

  ( noshort,
    "z3refresh",
    Const (Bool true),
    text "Restart Z3 after each query; useful for ensuring proof robustness");

  ( noshort,
    "z3rlimit",
    IntStr "positive_integer",
    text "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)");

  ( noshort,
    "z3rlimit_factor",
    IntStr "positive_integer",
    text "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)");

  ( noshort,
    "z3seed",
    IntStr "positive_integer",
    text "Set the Z3 random seed (default 0)");

  ( noshort,
    "z3version",
    SimpleStr "version",
    text "Set the version of Z3 that is to be used. Default: 4.8.5");

  ( noshort,
    "__no_positivity",
    WithSideEffect ((fun _ -> if warn_unsafe then option_warning_callback "__no_positivity"), Const (Bool true)),
    text "Don't check positivity of inductive types");

  ( noshort,
    "warn_error",
    ReverseAccumulated (SimpleStr ("")),
    text "The [-warn_error] option follows the OCaml syntax, namely:" ^^
    bulleted [
      text "[r] is a range of warnings (either a number [n], or a range [n..n])";
      text "[-r] silences range [r]";
      text "[+r] enables range [r] as warnings (NOTE: \"enabling\" an error will downgrade it to a warning)";
      text "[@r] makes range [r] fatal."
    ]);

  ( noshort,
    "use_nbe",
    BoolStr,
    text "Use normalization by evaluation as the default normalization strategy (default 'false')");

  ( noshort,
    "use_nbe_for_extraction",
    BoolStr,
    text "Use normalization by evaluation for normalizing terms before extraction (default 'false')");

  ( noshort,
   "trivial_pre_for_unannotated_effectful_fns",
    BoolStr,
    text "Enforce trivial preconditions for unannotated effectful functions (default 'true')" );

  ( noshort,
   "with_fstarc",
    Const (Bool true),
    text "Expose compiler internal modules (FStarC namespace). Only for advanced plugins \
          you should probably not use it.");

  ( noshort,
    "__debug_embedding",
    WithSideEffect ((fun _ -> debug_embedding := true),
                   (Const (Bool true))),
    text "Debug messages for embeddings/unembeddings of natively compiled terms");

  ( noshort,
    "eager_embedding",
     WithSideEffect ((fun _ -> eager_embedding := true),
                      (Const (Bool true))),
    text "Eagerly embed and unembed terms to primitive operations and plugins: not recommended except for benchmarking");

  ( noshort,
    "profile_group_by_decl",
     Const (Bool true),
    text "Emit profiles grouped by declaration rather than by module");

  ( noshort,
    "profile_component",
    Accumulated (SimpleStr "One or more space-separated occurrences of '[+|-]( * | namespace | module | identifier)'"),
    text "Specific source locations in the compiler are instrumented with profiling counters. \
          Pass `--profile_component FStarC.TypeChecker` to enable all counters in the FStarC.TypeChecker namespace. \
          This option is a module or namespace selector, like many other options (e.g., `--extract`)");

  ( noshort,
    "profile",
    Accumulated (SimpleStr "One or more space-separated occurrences of '[+|-]( * | namespace | module)'"),
    text "Profiling can be enabled when the compiler is processing a given set of source modules. \
          Pass `--profile FStar.Pervasives` to enable profiling when the compiler is processing any module in FStar.Pervasives. \
          This option is a module or namespace selector, like many other options (e.g., `--extract`)");

  ( 'h',
    "help",
     WithSideEffect ((fun _ -> display_usage_aux (specs warn_unsafe); exit 0),
                     (Const (Bool true))),
    text "Display this information");

  ( noshort,
    "list_debug_keys",
     WithSideEffect ((fun _ -> display_debug_keys(); exit 0),
                     (Const (Bool true))),
    text "List all debug keys and exit");

  (* FIXME: all of these should really be modes, not a boolean option *)
  ( noshort,
    "list_plugins",
     Const (Bool true),
    text "List all registered plugins and exit");
  ( noshort,
    "locate",
     Const (Bool true),
    text "Print the root of the F* installation and exit");
  ( noshort,
    "locate_lib",
    Const (Bool true),
    text "Print the root of the F* library and exit");
  ( noshort,
    "locate_ocaml",
    Const (Bool true),
    text "Print the root of the built OCaml F* library and exit");
  ( noshort,
    "locate_file",
    SimpleStr "basename",
    text "Find a file in F*'s include path and print its absolute path, then exit");
  ( noshort,
    "locate_z3",
    SimpleStr "version",
    text "Locate the executable for a given Z3 version, then exit. \
          The output is either an absolute path, or a name that was found in the PATH. \
          Note: this is the Z3 executable that F* will attempt to call for the given version, \
          but the version check is not performed at this point.");
  ( noshort,
    "ocamlenv",
    WithSideEffect ((fun _ -> print_error "--ocamlenv must be the first argument, see fstar.exe --help for details\n"; exit 1),
                     (Const (Bool true))),
    text "With no arguments: print shell code to set up an environment with the OCaml libraries in scope (similar to 'opam env'). \
          With arguments: run a command in that environment. \
          NOTE: this must be the FIRST argument passed to F* and other options are NOT processed.");
  ( noshort,
    "ocamlc",
    WithSideEffect ((fun _ -> print_error "--ocamlc must be the first argument, see fstar.exe --help for details\n"; exit 1),
                     (Const (Bool true))),
    text "A helper. This runs 'ocamlc' in the environment set up by --ocamlenv, for building an F* application bytecode executable.");
  ( noshort,
    "ocamlopt",
    WithSideEffect ((fun _ -> print_error "--ocamlopt must be the first argument, see fstar.exe --help for details\n"; exit 1),
                     (Const (Bool true))),
    text "A helper. This runs 'ocamlopt' in the environment set up by --ocamlenv, for building an F* application native executable.");
  ( noshort,
    "ocamlopt_plugin",
    WithSideEffect ((fun _ -> print_error "--ocamlopt_plugin must be the first argument, see fstar.exe --help for details\n"; exit 1),
                     (Const (Bool true))),
    text "A helper. This runs 'ocamlopt' in the environment set up by --ocamlenv, for building an F* plugin.");
  ]

and specs (warn_unsafe:bool) : list (FStarC.Getopt.opt & Pprint.document) =
  List.map (fun (short, long, typ, doc) ->
            mk_spec (short, long, arg_spec_of_opt_type long typ), doc)
           (specs_with_types warn_unsafe)

// Several options can only be set at the time the process is created,
// and not controlled interactively via pragmas.
// Additionaly, the --smt option is a security concern.
let settable = function
    | "__temp_fast_implicits"
    | "abort_on"
    | "admit_except"
    | "admit_smt_queries"
    | "compat_pre_core"
    | "compat_pre_typed_indexed_effects"
    | "disallow_unification_guards"
    | "debug"
    | "debug_all"
    | "debug_all_modules"
    | "defensive"
    | "detail_errors"
    | "detail_hint_replay"
    | "eager_subtyping"
    | "error_contexts"
    | "hide_uvar_nums"
    | "hint_dir"
    | "hint_file"
    | "hint_info"
    | "fuel"
    | "ext"
    | "ifuel"
    | "initial_fuel"
    | "initial_ifuel"
    | "ide_id_info_off"
    | "keep_query_captions"
    | "load"
    | "load_cmxs"
    | "log_queries"
    | "log_failing_queries"
    | "log_types"
    | "max_fuel"
    | "max_ifuel"
    | "no_plugins"
    | "__no_positivity"
    | "normalize_pure_terms_for_extraction"
    | "no_smt"
    | "no_tactics"
    | "print_bound_var_types"
    | "print_effect_args"
    | "print_expected_failures"
    | "print_full_names"
    | "print_implicits"
    | "print_universes"
    | "print_z3_statistics"
    | "prn"
    | "quake_lo"
    | "quake_hi"
    | "quake_keep"
    | "quake"
    | "query_cache"
    | "query_stats"
    | "record_options"
    | "retry"
    | "reuse_hint_for"
    | "report_assumes"
    | "silent"
    | "smtencoding.elim_box"
    | "smtencoding.l_arith_repr"
    | "smtencoding.nl_arith_repr"
    | "smtencoding.valid_intro"
    | "smtencoding.valid_elim"
    | "split_queries"
    | "tactic_raw_binders"
    | "tactics_failhard"
    | "tactics_info"
    | "__tactics_nbe"
    | "tactic_trace"
    | "tactic_trace_d"
    | "tcnorm"
    | "timing"
    | "trace_error"
    | "ugly"
    | "unthrottle_inductives"
    | "use_eq_at_higher_order"
    | "using_facts_from"
    | "warn_error"
    | "z3cliopt"
    | "z3smtopt"
    | "z3refresh"
    | "z3rlimit"
    | "z3rlimit_factor"
    | "z3seed"
    | "z3version"
    | "trivial_pre_for_unannotated_effectful_fns"
    | "profile_group_by_decl"
    | "profile_component"
    | "profile" -> true
    | _ -> false

let all_specs = specs true
let all_specs_getopt = List.map fst all_specs

let all_specs_with_types = specs_with_types true
let settable_specs = all_specs |> List.filter (fun ((_, x, _), _) -> settable x)

let help_for_option (s:string) : option Pprint.document =
  match all_specs |> List.filter (fun ((_, x, _), _) -> x = s) with
  | [] -> None
  | o::_ -> Some (usage_for o) // NB: there should be only one

/////////////////////////////////////////////////////////////////////////////////////////////////////////
//PUBLIC API
/////////////////////////////////////////////////////////////////////////////////////////////////////////
let set_error_flags_callback_aux,
    set_error_flags =
    let callback : ref (option (unit -> parse_cmdline_res)) = mk_ref None in
    let set f = callback := Some f in
    let call () =
      match !callback with
      | None -> failwith "Error flags callback not yet set"
      | Some f -> f ()
    in
    set, call

let set_error_flags_callback = set_error_flags_callback_aux
let display_usage () = display_usage_aux all_specs

let fstar_bin_directory = Util.get_exec_dir ()

let file_list_ : ref (list string) = Util.mk_ref []

(* In `parse_filename_arg specs arg`:

   * `arg` is a filename argument to be parsed. If `arg` is of the
     form `@file`, then `file` is a response file, from which further
     arguments (including further options) are read. Nested response
     files (@ response file arguments within response files) are
     supported.

   * `specs` is the list of option specifications (- and --)

   * `enable_filenames` is a boolean, true if non-response file
   * filenames should be handled.

*)


let rec parse_filename_arg specs enable_filenames arg =
  if Util.starts_with arg "@"
  then begin
    // read and parse a response file
    let filename = Util.substring_from arg 1 in
    let lines = Util.file_get_lines filename in
    Getopt.parse_list specs (parse_filename_arg specs enable_filenames) lines
  end else begin
    if enable_filenames
    then file_list_ := !file_list_ @ [arg];
    Success
  end

let parse_cmd_line () =
  let res = Getopt.parse_cmdline all_specs_getopt (parse_filename_arg all_specs_getopt true) in
  let res =
    if res = Success
    then set_error_flags()
    else res
  in
  res, !file_list_

let file_list () =
  !file_list_

let restore_cmd_line_options should_clear =
    (* Some options must be preserved because they can't be reset via #pragrams.
     * Add them here as needed. *)
    let old_verify_module = get_verify_module() in
    if should_clear then clear() else init();
    let specs = List.map fst <| specs false in
    let r = Getopt.parse_cmdline specs (parse_filename_arg specs false) in
    set_option' ("verify_module", List (List.map String old_verify_module));
    r

let module_name_of_file_name f =
    let f = basename f in
    let f = String.substring f 0 (String.length f - String.length (get_file_extension f) - 1) in
    String.lowercase f

let should_check m =
  let l = get_verify_module () in
  List.contains (String.lowercase m) l

let should_verify m =
  not (get_lax ()) && should_check m

let should_check_file fn =
    should_check (module_name_of_file_name fn)

let should_verify_file fn =
    should_verify (module_name_of_file_name fn)

let module_name_eq m1 m2 = String.lowercase m1 = String.lowercase m2

let should_print_message m =
    if should_verify m
    then m <> "Prims"
    else false


let custom_prims () = get_prims()

let cache_dir () = get_cache_dir ()

let include_ () = get_include ()

//Used to parse the options of
//   --using_facts_from
//   --extract
//   --already_cached
let path_of_text text = String.split ['.'] text

let parse_settings ns : list (list string & bool) =
    let cache = Util.smap_create 31 in
    let with_cache f s =
      match Util.smap_try_find cache s with
      | Some s -> s
      | None ->
        let res = f s in
        Util.smap_add cache s res;
        res
    in
    let parse_one_setting s =
        if s = "*" then ([], true)
        else if s = "-*" then ([], false)
        else if Util.starts_with s "-"
        then let path = path_of_text (Util.substring_from s 1) in
             (path, false)
        else let s = if Util.starts_with s "+"
                     then Util.substring_from s 1
                     else s in
             (path_of_text s, true)
    in
    ns |> List.collect (fun s ->
      let s = Util.trim_string s in
      if s = "" then []
      else with_cache (fun s ->
             let s = Util.replace_char s ' ' ',' in
             Util.splitlines s
             |> List.concatMap (fun s -> Util.split s ",")
             |> List.filter (fun s -> s <> "")
             |> List.map parse_one_setting) s)
             |> List.rev

let admit_smt_queries            () = get_admit_smt_queries           ()
let admit_except                 () = get_admit_except                ()
let compat_pre_core_should_register () =
  match get_compat_pre_core() with
  | Some 0 -> false
  | _ -> true
let compat_pre_core_should_check () =
  match get_compat_pre_core() with
  | Some 0
  | Some 1 -> false
  | _ -> true
let compat_pre_core_set () =
  match get_compat_pre_core() with
  | None -> false
  | _ -> true

let compat_pre_typed_indexed_effects () = get_compat_pre_typed_indexed_effects ()

let disallow_unification_guards  () = get_disallow_unification_guards    ()
let cache_checked_modules        () = get_cache_checked_modules       ()
let cache_off                    () = get_cache_off                   ()
let print_cache_version          () = get_print_cache_version         ()
let cmi                          () = get_cmi                         ()

let parse_codegen =
  function
  | "OCaml" -> Some OCaml
  | "FSharp" -> Some FSharp
  | "krml" -> Some Krml
  | "Plugin" -> Some Plugin
  | "PluginNoLib" -> Some PluginNoLib
  | "Extension" -> Some Extension
  | _ -> None

let print_codegen =
  function
  | OCaml -> "OCaml"
  | FSharp -> "FSharp"
  | Krml -> "krml"
  | Plugin -> "Plugin"
  | PluginNoLib -> "PluginNoLib"
  | Extension -> "Extension"

let codegen                      () =
    Util.map_opt (get_codegen())
                 (fun s -> parse_codegen s |> must)

let codegen_libs                 () = get_codegen_lib () |> List.map (fun x -> Util.split x ".")

let profile_group_by_decl        () = get_profile_group_by_decl ()
let defensive                    () = get_defensive () <> "no"
let defensive_error              () = get_defensive () = "error"
let defensive_abort              () = get_defensive () = "abort"
let dep                          () = get_dep                         ()
let detail_errors                () = get_detail_errors               ()
let detail_hint_replay           () = get_detail_hint_replay          ()
let any_dump_module              () = Cons? (get_dump_module())
let dump_module                  s  = get_dump_module() |> List.existsb (module_name_eq s)
let eager_subtyping              () = get_eager_subtyping()
let error_contexts               () = get_error_contexts              ()
let expose_interfaces            () = get_expose_interfaces          ()
let interactive                  () = get_in () || get_ide () || get_lsp ()
let message_format               () =
  match get_message_format () with
  | "auto" -> (
    if interactive () then Human
    else
    match Util.expand_environment_variable "GITHUB_ACTIONS" with
    | None
    | Some "" -> Human
    | Some _ -> Github
  )
  | "human" -> Human
  | "json" -> Json
  | "github" -> Github
  | illegal -> failwith ("print_issue: option `message_format` was expected to be `human` or `json`, not `" ^ illegal ^ "`. This should be impossible: `message_format` was supposed to be validated.")
let force                        () = get_force                       ()
let full_context_dependency      () = true
let hide_uvar_nums               () = get_hide_uvar_nums              ()
let hint_info                    () = get_hint_info                   ()
                                    || get_query_stats                ()
let hint_dir                     () = get_hint_dir                    ()
let hint_file                    () = get_hint_file                   ()
let hint_file_for_src src_filename =
      match hint_file() with
      | Some fn -> fn
      | None ->
        let file_name =
          match hint_dir () with
          | Some dir ->
            Util.concat_dir_filename dir (Util.basename src_filename)
          | _ -> src_filename
        in
        Util.format1 "%s.hints" file_name
let ide                          () = get_ide                         ()
let ide_id_info_off              () = get_ide_id_info_off             ()
let ide_file_name_st =
  let v = Util.mk_ref (None #string) in
  let set f =
    match !v with
    | None -> v := Some f
    | Some _ -> failwith "ide_file_name_st already set" in
  let get () = !v in
  set, get
let set_ide_filename = fst ide_file_name_st
let ide_filename = snd ide_file_name_st
let print                        () = get_print                       ()
let print_in_place               () = get_print_in_place              ()
let initial_fuel                 () = min (get_initial_fuel ()) (get_max_fuel ())
let initial_ifuel                () = min (get_initial_ifuel ()) (get_max_ifuel ())
let lax                          () = get_lax                         ()
let load                         () = get_load                        ()
let load_cmxs                    () = get_load_cmxs                   ()
let legacy_interactive           () = get_in                          ()
let lsp_server                   () = get_lsp                         ()
let log_queries                  () = get_log_queries                 ()
let log_failing_queries          () = get_log_failing_queries         ()
let keep_query_captions          () =
    get_keep_query_captions ()
    && (log_queries () || log_failing_queries ())

let log_types                    () = get_log_types                   ()
let max_fuel                     () = get_max_fuel                    ()
let max_ifuel                    () = get_max_ifuel                   ()
let ml_ish                       () = get_MLish                       ()
let ml_ish_effect                () = get_MLish_effect                ()
let set_ml_ish                   () = set_option "MLish" (Bool true)
let no_default_includes          () = get_no_default_includes         ()
let no_extract                   s  = get_no_extract() |> List.existsb (module_name_eq s)
let normalize_pure_terms_for_extraction
                                 () = get_normalize_pure_terms_for_extraction ()
let no_location_info             () = get_no_location_info            ()
let no_plugins                   () = get_no_plugins                  ()
let no_smt                       () = get_no_smt                      ()
let krmloutput                   () = get_krmloutput                  ()
let output_dir                   () = get_odir                        ()
let output_deps_to               () = get_output_deps_to              ()
let ugly                         () = get_ugly                        ()
let print_bound_var_types        () = get_print_bound_var_types       ()
let print_effect_args            () = get_print_effect_args           ()
let print_expected_failures      () = get_print_expected_failures     ()
let print_implicits              () = get_print_implicits             ()
let print_real_names             () = get_prn () || get_print_full_names()
let print_universes              () = get_print_universes             ()
let print_z3_statistics          () = get_print_z3_statistics         ()
let proof_recovery               () = get_proof_recovery              ()
let quake_lo                     () = get_quake_lo                    ()
let quake_hi                     () = get_quake_hi                    ()
let quake_keep                   () = get_quake_keep                  ()
let query_cache                  () = get_query_cache                 ()
let query_stats                  () = get_query_stats                 ()
let read_checked_file            () = get_read_checked_file           ()
let list_plugins                 () = get_list_plugins                ()
let locate                       () = get_locate                      ()
let locate_lib                   () = get_locate_lib                  ()
let locate_ocaml                 () = get_locate_ocaml                ()
let locate_file                  () = get_locate_file                 ()
let locate_z3                    () = get_locate_z3                   ()
let read_krml_file               () = get_read_krml_file              ()
let record_hints                 () = get_record_hints                ()
let record_options               () = get_record_options              ()
let retry                        () = get_retry                       ()
let reuse_hint_for               () = get_reuse_hint_for              ()
let report_assumes               () = get_report_assumes              ()
let silent                       () = get_silent                      ()
let smt                          () = get_smt                         ()
let smtencoding_elim_box         () = get_smtencoding_elim_box        ()
let smtencoding_nl_arith_native  () = get_smtencoding_nl_arith_repr () = "native"
let smtencoding_nl_arith_wrapped () = get_smtencoding_nl_arith_repr () = "wrapped"
let smtencoding_nl_arith_default () = get_smtencoding_nl_arith_repr () = "boxwrap"
let smtencoding_l_arith_native   () = get_smtencoding_l_arith_repr () = "native"
let smtencoding_l_arith_default  () = get_smtencoding_l_arith_repr () = "boxwrap"
let smtencoding_valid_intro      () = get_smtencoding_valid_intro     ()
let smtencoding_valid_elim       () = get_smtencoding_valid_elim      ()

let parse_split_queries (s:string) : option split_queries_t =
  match s with
  | "no" -> Some No
  | "on_failure" -> Some OnFailure
  | "always" -> Some Always
  | _ -> None

let split_queries                () = get_split_queries () |> parse_split_queries |> Util.must
let tactic_raw_binders           () = get_tactic_raw_binders          ()
let tactics_failhard             () = get_tactics_failhard            ()
let tactics_info                 () = get_tactics_info                ()
let tactic_trace                 () = get_tactic_trace                ()
let tactic_trace_d               () = get_tactic_trace_d              ()
let tactics_nbe                  () = get_tactics_nbe                 ()
let tcnorm                       () = get_tcnorm                      ()
let timing                       () = get_timing                      ()
let trace_error                  () = get_trace_error                 ()
let unthrottle_inductives        () = get_unthrottle_inductives       ()
let unsafe_tactic_exec           () = get_unsafe_tactic_exec          ()
let use_eq_at_higher_order       () = get_use_eq_at_higher_order      ()
let use_hints                    () = get_use_hints                   ()
let use_hint_hashes              () = get_use_hint_hashes             ()
let use_native_tactics           () = get_use_native_tactics          ()
let use_tactics                  () = not (get_no_tactics             ())
let using_facts_from             () =
    match get_using_facts_from () with
    | None -> [ [], true ] //if not set, then retain all facts
    | Some ns -> parse_settings ns
let warn_default_effects         () = get_warn_default_effects        ()
let warn_error                   () = String.concat " " (get_warn_error())
let z3_cliopt                    () = get_z3cliopt                    ()
let z3_smtopt                    () = get_z3smtopt                    ()
let z3_refresh                   () = get_z3refresh                   ()
let z3_rlimit                    () = get_z3rlimit                    ()
let z3_rlimit_factor             () = get_z3rlimit_factor             ()
let z3_seed                      () = get_z3seed                      ()
let z3_version                   () = get_z3version                   ()
let no_positivity                () = get_no_positivity               ()
let use_nbe                      () = get_use_nbe                     ()
let use_nbe_for_extraction       () = get_use_nbe_for_extraction      ()
let trivial_pre_for_unannotated_effectful_fns
                                 () = get_trivial_pre_for_unannotated_effectful_fns ()
let with_fstarc                  () = get_with_fstarc ()

let debug_keys                   () = lookup_opt "debug" as_comma_string_list
let debug_all                    () = lookup_opt "debug_all" as_bool
let debug_all_modules            () = lookup_opt "debug_all_modules" as_bool

let with_saved_options f =
  // take some care to not mess up the stack on errors
  // (unless we're trying to track down an error)
  // TODO: This assumes `f` does not mess with the stack!
  if not (trace_error ()) then begin
      push ();
      let r = try Inr (f ()) with | ex -> Inl ex in
      pop ();
      match r with
      | Inr v  -> v
      | Inl ex -> raise ex
  end else begin
      push ();
      let retv = f () in
      pop ();
      retv
  end

let module_matches_namespace_filter m filter =
    let m = String.lowercase m in
    let setting = parse_settings filter in
    let m_components = path_of_text m in
    let rec matches_path m_components path =
        match m_components, path with
        | _, [] -> true
        | m::ms, p::ps -> m=String.lowercase p && matches_path ms ps
        | _ -> false
    in
    match setting
          |> Util.try_find
              (fun (path, _) -> matches_path m_components path)
    with
    | None -> false
    | Some (_, flag) -> flag

let matches_namespace_filter_opt m =
  function
  | None -> false
  | Some filter -> module_matches_namespace_filter m filter

type parsed_extract_setting = {
  target_specific_settings: list (codegen_t & string);
  default_settings:option string
}

let print_pes pes =
  Util.format2 "{ target_specific_settings = %s;\n\t
               default_settings = %s }"
            (List.map (fun (tgt, s) ->
                         Util.format2 "(%s, %s)"
                           (print_codegen tgt)
                           s)
                      pes.target_specific_settings
             |> String.concat "; ")
            (match pes.default_settings with
             | None -> "None"
             | Some s -> s)

let find_setting_for_target tgt (s:list (codegen_t & string))
  : option string
  = match Util.try_find (fun (x, _) -> x = tgt) s with
    | Some (_, s) -> Some s
    | _ -> None

let extract_settings
  : unit -> option parsed_extract_setting
  = let memo:ref (option parsed_extract_setting & bool) = Util.mk_ref (None, false) in
    let merge_parsed_extract_settings p0 p1 : parsed_extract_setting =
      let merge_setting s0 s1 =
        match s0, s1 with
        | None, None -> None
        | Some p, None
        | None, Some p -> Some p
        | Some p0, Some p1 -> Some (p0 ^ "," ^ p1)
      in
      let merge_target tgt =
        match
          merge_setting
            (find_setting_for_target tgt p0.target_specific_settings)
            (find_setting_for_target tgt p1.target_specific_settings)
        with
        | None -> []
        | Some x -> [tgt,x]
      in
      {
        target_specific_settings = List.collect merge_target [OCaml;FSharp;Krml;Plugin;PluginNoLib;Extension];
        default_settings = merge_setting p0.default_settings p1.default_settings
      }
    in
    fun _ ->
      let result, set = !memo in
      let fail msg =
           display_usage();
           failwith (Util.format1 "Could not parse '%s' passed to the --extract option" msg)
      in
      if set then result
      else match get_extract () with
           | None ->
             memo := (None, true);
             None

           | Some extract_settings ->
             let parse_one_setting extract_setting =
               // T1:setting1; T2:setting2; ... or
               // setting <-- applies to all other targets
               let tgt_specific_settings = Util.split extract_setting ";" in
               let split_one t_setting =
                   match Util.split t_setting ":" with
                   | [default_setting] ->
                     Inr (Util.trim_string default_setting)
                   | [target; setting] ->
                     let target = Util.trim_string target in
                     match parse_codegen target with
                     | None -> fail target
                     | Some tgt -> Inl (tgt, Util.trim_string setting)
                   | _ -> fail t_setting
               in
               let settings = List.map split_one tgt_specific_settings in
               let fail_duplicate msg tgt =
                   display_usage();
                   failwith
                     (Util.format2
                       "Could not parse '%s'; multiple setting for %s target"
                       msg tgt)
               in
               let pes =
                 List.fold_right
                   (fun setting out ->
                     match setting with
                     | Inr def ->
                       (match out.default_settings with
                         | None -> { out with default_settings = Some def }
                         | Some _ ->  fail_duplicate def "default")
                     | Inl (target, setting) ->
                       (match Util.try_find (fun (x, _) -> x = target) out.target_specific_settings with
                         | None -> { out with target_specific_settings = (target, setting):: out.target_specific_settings }
                         | Some _ -> fail_duplicate setting (print_codegen target)))
                   settings
                   ({ target_specific_settings = []; default_settings = None })
               in
               pes
             in
             let empty_pes = { target_specific_settings = []; default_settings = None } in
             let pes =
               //the left-most settings on the command line are at the end of the list
               //so fold_right
               List.fold_right
                 (fun setting pes -> merge_parsed_extract_settings pes (parse_one_setting setting))
                 extract_settings
                 empty_pes
             in
             memo := (Some pes, true);
             Some pes

let should_extract (m:string) (tgt:codegen_t) : bool =
    let m = String.lowercase m in
    if m = "prims" then false
    else
    match extract_settings() with
    | Some pes -> //new option, using --extract 'OCaml:* -FStar' etc.
      let _ =
        match get_no_extract(),
              get_extract_namespace(),
              get_extract_module ()
        with
        | [], [], [] -> ()
        | _ -> failwith "Incompatible options: \
                        --extract cannot be used with \
                        --no_extract, --extract_namespace or --extract_module"
      in
      let tsetting =
        match find_setting_for_target tgt pes.target_specific_settings with
        | Some s -> s
        | None ->
          match pes.default_settings with
          | Some s -> s
          | None -> "*" //extract everything, by default
      in
      module_matches_namespace_filter m [tsetting]
    | None -> //old
        let should_extract_namespace m =
            match get_extract_namespace () with
            | [] -> false
            | ns -> ns |> Util.for_some (fun n -> Util.starts_with m (String.lowercase n))
        in
        let should_extract_module m =
            match get_extract_module () with
            | [] -> false
            | l -> l |> Util.for_some (fun n -> String.lowercase n = m)
        in
        not (no_extract m) &&
        (match get_extract_namespace (), get_extract_module() with
        | [], [] -> true //neither is set; extract everything
        | _ -> should_extract_namespace m || should_extract_module m)

let should_be_already_cached m =
  (* should_check is true for files in the command line,
  we exclude those from this check since they were explicitly
  requested. *)
  not (should_check m) && (
    match get_already_cached() with
    | None -> false
    | Some already_cached_setting ->
      module_matches_namespace_filter m already_cached_setting
  )


let profile_enabled modul_opt phase =
  match modul_opt with
  | None -> //the phase is not associated with a module
    matches_namespace_filter_opt phase (get_profile_component())

  | Some modul ->
    (matches_namespace_filter_opt modul (get_profile())
     && matches_namespace_filter_opt phase (get_profile_component()))

    // A special case for --timing: this option should print the time
    // taken for each top-level decl, so we enable the profiler only for
    // the FStarC.TypeChecker.process_one_decl phase, and only for those
    // modules given in the command line.
    || (timing ()
        && phase = "FStarC.TypeChecker.Tc.process_one_decl"
        && should_check modul)

exception File_argument of string

let set_options s =
    try
        if s = ""
        then Success
        else let settable_specs = List.map fst settable_specs in
             let res = Getopt.parse_string settable_specs (fun s -> raise (File_argument s); Error ("set_options with file argument", "")) s in
             if res=Success
             then set_error_flags()
             else res
    with
    | File_argument s -> Getopt.Error (Util.format1 "File %s is not a valid option" s, "")

let with_options s f =
  with_saved_options (fun () ->
    ignore (set_options s);
    f ())

let get_vconfig () =
  let vcfg = {
    initial_fuel                              = get_initial_fuel ();
    max_fuel                                  = get_max_fuel ();
    initial_ifuel                             = get_initial_ifuel ();
    max_ifuel                                 = get_max_ifuel ();
    detail_errors                             = get_detail_errors ();
    detail_hint_replay                        = get_detail_hint_replay ();
    no_smt                                    = get_no_smt ();
    quake_lo                                  = get_quake_lo ();
    quake_hi                                  = get_quake_hi ();
    quake_keep                                = get_quake_keep ();
    retry                                     = get_retry ();
    smtencoding_elim_box                      = get_smtencoding_elim_box ();
    smtencoding_nl_arith_repr                 = get_smtencoding_nl_arith_repr ();
    smtencoding_l_arith_repr                  = get_smtencoding_l_arith_repr ();
    smtencoding_valid_intro                   = get_smtencoding_valid_intro ();
    smtencoding_valid_elim                    = get_smtencoding_valid_elim ();
    tcnorm                                    = get_tcnorm ();
    no_plugins                                = get_no_plugins ();
    no_tactics                                = get_no_tactics ();
    z3cliopt                                  = get_z3cliopt ();
    z3smtopt                                  = get_z3smtopt ();
    z3refresh                                 = get_z3refresh ();
    z3rlimit                                  = get_z3rlimit ();
    z3rlimit_factor                           = get_z3rlimit_factor ();
    z3seed                                    = get_z3seed ();
    z3version                                 = get_z3version ();
    trivial_pre_for_unannotated_effectful_fns = get_trivial_pre_for_unannotated_effectful_fns ();
    reuse_hint_for                            = get_reuse_hint_for ();
  }
  in
  vcfg

let set_vconfig (vcfg:vconfig) : unit =
  let option_as (tag : 'a -> option_val) (o : option 'a) : option_val =
    match o with
    | None -> Unset
    | Some s -> tag s
  in
  set_option "initial_fuel"                              (Int vcfg.initial_fuel);
  set_option "max_fuel"                                  (Int vcfg.max_fuel);
  set_option "initial_ifuel"                             (Int vcfg.initial_ifuel);
  set_option "max_ifuel"                                 (Int vcfg.max_ifuel);
  set_option "detail_errors"                             (Bool vcfg.detail_errors);
  set_option "detail_hint_replay"                        (Bool vcfg.detail_hint_replay);
  set_option "no_smt"                                    (Bool vcfg.no_smt);
  set_option "quake_lo"                                  (Int vcfg.quake_lo);
  set_option "quake_hi"                                  (Int vcfg.quake_hi);
  set_option "quake_keep"                                (Bool vcfg.quake_keep);
  set_option "retry"                                     (Bool vcfg.retry);
  set_option "smtencoding.elim_box"                      (Bool vcfg.smtencoding_elim_box);
  set_option "smtencoding.nl_arith_repr"                 (String vcfg.smtencoding_nl_arith_repr);
  set_option "smtencoding.l_arith_repr"                  (String vcfg.smtencoding_l_arith_repr);
  set_option "smtencoding.valid_intro"                   (Bool vcfg.smtencoding_valid_intro);
  set_option "smtencoding.valid_elim"                    (Bool vcfg.smtencoding_valid_elim);
  set_option "tcnorm"                                    (Bool vcfg.tcnorm);
  set_option "no_plugins"                                (Bool vcfg.no_plugins);
  set_option "no_tactics"                                (Bool vcfg.no_tactics);
  set_option "z3cliopt"                                  (List (List.map String vcfg.z3cliopt));
  set_option "z3smtopt"                                  (List (List.map String vcfg.z3smtopt));
  set_option "z3refresh"                                 (Bool vcfg.z3refresh);
  set_option "z3rlimit"                                  (Int vcfg.z3rlimit);
  set_option "z3rlimit_factor"                           (Int vcfg.z3rlimit_factor);
  set_option "z3seed"                                    (Int vcfg.z3seed);
  set_option "z3version"                                 (String vcfg.z3version);
  set_option "trivial_pre_for_unannotated_effectful_fns" (Bool vcfg.trivial_pre_for_unannotated_effectful_fns);
  set_option "reuse_hint_for"                            (option_as String vcfg.reuse_hint_for);
  ()

instance showable_codegen_t : showable codegen_t = {
  show = print_codegen;
}

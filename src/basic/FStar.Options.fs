(*
   Copyright 2008-2014 Nikhil Swamy and Microsoft Research

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
#light "off"

// (c) Microsoft Corporation. All rights reserved
module FStar.Options
open FStar.ST
open FStar.Exn
open FStar.All
open FStar
open FStar.Util
open FStar.Getopt
open FStar.BaseTypes

module FC = FStar.Common

type debug_level_t =
  | Low
  | Medium
  | High
  | Extreme
  | Other of string

type option_val =
  | Bool of bool
  | String of string
  | Path of string
  | Int of int
  | List of list<option_val>
  | Unset

//These wrappers provide each constructor with the ML effect
//They are needed to make type-inference work well with the
//--eager_inference flag that is used during bootstrapping,
//which explicitly disables some subtyping/sub-effecting
let mk_bool   : bool -> option_val = Bool
let mk_string : string -> option_val = String
let mk_path   : string -> option_val = Path
let mk_int    : int -> option_val = Int
let mk_list   : list<option_val> -> option_val = List

type options =
    | Set
    | Reset
    | Restore



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
  | Path b -> FStar.Common.try_convert_file_name_to_mixed b
  | _ -> failwith "Impos: expected String"
let as_list' = function
  | List ts -> ts
  | _ -> failwith "Impos: expected List"
let as_list as_t x =
  as_list' x |> List.map as_t
let as_option as_t = function
  | Unset -> None
  | v -> Some (as_t v)

type optionstate = Util.smap<option_val>

let fstar_options : ref<list<optionstate> > = Util.mk_ref []
let peek () = List.hd !fstar_options
let pop  () =
    match !fstar_options with
    | []
    | [_] -> failwith "TOO MANY POPS!"
    | _::tl -> fstar_options := tl
let push () = fstar_options := Util.smap_copy (peek()) :: !fstar_options
let set o =
    match !fstar_options with
    | [] -> failwith "set on empty option stack"
    | _::os -> fstar_options := (o::os)

let set_option k v = Util.smap_add (peek()) k v
let set_option' (k,v) =  set_option k v

let with_saved_options f =
  push (); let retv = f () in pop (); retv

let light_off_files : ref<list<string>> = Util.mk_ref []
let add_light_off_file (filename:string) = light_off_files := filename :: !light_off_files

let defaults =
     [
      ("__temp_no_proj"               , List []);
      ("admit_smt_queries"            , Bool false);
      ("admit_except"                 , Unset);
      ("cache_checked_modules"        , Bool false);
      ("codegen"                      , Unset);
      ("codegen-lib"                  , List []);
      ("debug"                        , List []);
      ("debug_level"                  , List []);
      ("dep"                          , Unset);
      ("detail_errors"                , Bool false);
      ("detail_hint_replay"           , Bool false);
      ("doc"                          , Bool false);
      ("dump_module"                  , List []);
      ("eager_inference"              , Bool false);
      ("expose_interfaces"            , Bool false);
      ("extract"                      , Unset);
      ("extract_all"                  , Bool false);
      ("extract_module"               , List []);
      ("extract_namespace"            , List []);
      ("fs_typ_app"                   , Bool false);
      ("fstar_home"                   , Unset);
      ("full_context_dependency"      , Bool true);
      ("gen_native_tactics"           , Unset);
      ("hide_uvar_nums"               , Bool false);
      ("hint_info"                    , Bool false);
      ("hint_file"                    , Unset);
      ("in"                           , Bool false);
      ("ide"                          , Bool false);
      ("include"                      , List []);
      ("indent"                       , Bool false);
      ("initial_fuel"                 , Int 2);
      ("initial_ifuel"                , Int 1);
      ("lax"                          , Bool false);
      ("load"                         , List []);
      ("log_queries"                  , Bool false);
      ("log_types"                    , Bool false);
      ("max_fuel"                     , Int 8);
      ("max_ifuel"                    , Int 2);
      ("min_fuel"                     , Int 1);
      ("MLish"                        , Bool false);
      ("n_cores"                      , Int 1);
      ("no_default_includes"          , Bool false);
      ("no_extract"                   , List []);
      ("no_location_info"             , Bool false);
      ("no_tactics"                   , Bool false);
      ("odir"                         , Unset);
      ("prims"                        , Unset);
      ("pretype"                      , Bool true);
      ("prims_ref"                    , Unset);
      ("print_bound_var_types"        , Bool false);
      ("print_effect_args"            , Bool false);
      ("print_full_names"             , Bool false);
      ("print_implicits"              , Bool false);
      ("print_universes"              , Bool false);
      ("print_z3_statistics"          , Bool false);
      ("prn"                          , Bool false);
      ("query_stats"                  , Bool false);
      ("record_hints"                 , Bool false);
      ("reuse_hint_for"               , Unset);
      ("silent"                       , Bool false);
      ("smt"                          , Unset);
      ("smtencoding.elim_box"         , Bool false);
      ("smtencoding.nl_arith_repr"    , String "boxwrap");
      ("smtencoding.l_arith_repr"     , String "boxwrap");
      ("tactic_raw_binders"           , Bool false);
      ("tactic_trace"                 , Bool false);
      ("tactic_trace_d"               , Int 0);
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
      ("vcgen.optimize_bind_as_seq"   , Unset);
      ("verify_module"                , List []);
      ("warn_default_effects"         , Bool false);
      ("z3refresh"                    , Bool false);
      ("z3rlimit"                     , Int 5);
      ("z3rlimit_factor"              , Int 1);
      ("z3seed"                       , Int 0);
      ("z3cliopt"                     , List []);
      ("use_two_phase_tc"             , Bool false);
      ("__no_positivity"              , Bool false);
      ("__ml_no_eta_expand_coertions" , Bool false);
      ("warn_error"                   , String "")]

let init () =
   let o = peek () in
   Util.smap_clear o;
   defaults |> List.iter set_option'                          //initialize it with the default values

let clear () =
   let o = Util.smap_create 50 in
   fstar_options := [o];                                 //clear and reset the options stack
   light_off_files := [];
   init()

let _run = clear()

let get_option s =
  match Util.smap_try_find (peek()) s with
  | None -> failwith ("Impossible: option " ^s^ " not found")
  | Some s -> s

let lookup_opt s c =
  c (get_option s)

let get_admit_smt_queries       ()      = lookup_opt "admit_smt_queries"        as_bool
let get_admit_except            ()      = lookup_opt "admit_except"             (as_option as_string)
let get_cache_checked_modules   ()      = lookup_opt "cache_checked_modules"    as_bool
let get_codegen                 ()      = lookup_opt "codegen"                  (as_option as_string)
let get_codegen_lib             ()      = lookup_opt "codegen-lib"              (as_list as_string)
let get_debug                   ()      = lookup_opt "debug"                    (as_list as_string)
let get_debug_level             ()      = lookup_opt "debug_level"              (as_list as_string)
let get_dep                     ()      = lookup_opt "dep"                      (as_option as_string)
let get_detail_errors           ()      = lookup_opt "detail_errors"            as_bool
let get_detail_hint_replay      ()      = lookup_opt "detail_hint_replay"       as_bool
let get_doc                     ()      = lookup_opt "doc"                      as_bool
let get_dump_module             ()      = lookup_opt "dump_module"              (as_list as_string)
let get_eager_inference         ()      = lookup_opt "eager_inference"          as_bool
let get_expose_interfaces       ()      = lookup_opt "expose_interfaces"        as_bool
let get_extract                 ()      = lookup_opt "extract"                  (as_option (as_list as_string))
let get_extract_module          ()      = lookup_opt "extract_module"           (as_list as_string)
let get_extract_namespace       ()      = lookup_opt "extract_namespace"        (as_list as_string)
let get_fs_typ_app              ()      = lookup_opt "fs_typ_app"               as_bool
let get_fstar_home              ()      = lookup_opt "fstar_home"               (as_option as_string)
let get_gen_native_tactics      ()      = lookup_opt "gen_native_tactics"       (as_option as_string)
let get_hide_uvar_nums          ()      = lookup_opt "hide_uvar_nums"           as_bool
let get_hint_info               ()      = lookup_opt "hint_info"                as_bool
let get_hint_file               ()      = lookup_opt "hint_file"                (as_option as_string)
let get_in                      ()      = lookup_opt "in"                       as_bool
let get_ide                     ()      = lookup_opt "ide"                      as_bool
let get_include                 ()      = lookup_opt "include"                  (as_list as_string)
let get_indent                  ()      = lookup_opt "indent"                   as_bool
let get_initial_fuel            ()      = lookup_opt "initial_fuel"             as_int
let get_initial_ifuel           ()      = lookup_opt "initial_ifuel"            as_int
let get_lax                     ()      = lookup_opt "lax"                      as_bool
let get_load                    ()      = lookup_opt "load"                     (as_list as_string)
let get_log_queries             ()      = lookup_opt "log_queries"              as_bool
let get_log_types               ()      = lookup_opt "log_types"                as_bool
let get_max_fuel                ()      = lookup_opt "max_fuel"                 as_int
let get_max_ifuel               ()      = lookup_opt "max_ifuel"                as_int
let get_min_fuel                ()      = lookup_opt "min_fuel"                 as_int
let get_MLish                   ()      = lookup_opt "MLish"                    as_bool
let get_n_cores                 ()      = lookup_opt "n_cores"                  as_int
let get_no_default_includes     ()      = lookup_opt "no_default_includes"      as_bool
let get_no_extract              ()      = lookup_opt "no_extract"               (as_list as_string)
let get_no_location_info        ()      = lookup_opt "no_location_info"         as_bool
let get_odir                    ()      = lookup_opt "odir"                     (as_option as_string)
let get_ugly                    ()      = lookup_opt "ugly"                     as_bool
let get_prims                   ()      = lookup_opt "prims"                    (as_option as_string)
let get_print_bound_var_types   ()      = lookup_opt "print_bound_var_types"    as_bool
let get_print_effect_args       ()      = lookup_opt "print_effect_args"        as_bool
let get_print_full_names        ()      = lookup_opt "print_full_names"         as_bool
let get_print_implicits         ()      = lookup_opt "print_implicits"          as_bool
let get_print_universes         ()      = lookup_opt "print_universes"          as_bool
let get_print_z3_statistics     ()      = lookup_opt "print_z3_statistics"      as_bool
let get_prn                     ()      = lookup_opt "prn"                      as_bool
let get_query_stats             ()      = lookup_opt "query_stats"              as_bool
let get_record_hints            ()      = lookup_opt "record_hints"             as_bool
let get_reuse_hint_for          ()      = lookup_opt "reuse_hint_for"           (as_option as_string)
let get_silent                  ()      = lookup_opt "silent"                   as_bool
let get_smt                     ()      = lookup_opt "smt"                      (as_option as_string)
let get_smtencoding_elim_box    ()      = lookup_opt "smtencoding.elim_box"     as_bool
let get_smtencoding_nl_arith_repr ()    = lookup_opt "smtencoding.nl_arith_repr" as_string
let get_smtencoding_l_arith_repr()      = lookup_opt "smtencoding.l_arith_repr" as_string
let get_tactic_raw_binders      ()      = lookup_opt "tactic_raw_binders"       as_bool
let get_tactic_trace            ()      = lookup_opt "tactic_trace"             as_bool
let get_tactic_trace_d          ()      = lookup_opt "tactic_trace_d"           as_int
let get_timing                  ()      = lookup_opt "timing"                   as_bool
let get_trace_error             ()      = lookup_opt "trace_error"              as_bool
let get_unthrottle_inductives   ()      = lookup_opt "unthrottle_inductives"    as_bool
let get_unsafe_tactic_exec      ()      = lookup_opt "unsafe_tactic_exec"       as_bool
let get_use_eq_at_higher_order  ()      = lookup_opt "use_eq_at_higher_order"   as_bool
let get_use_hints               ()      = lookup_opt "use_hints"                as_bool
let get_use_hint_hashes         ()      = lookup_opt "use_hint_hashes"          as_bool
let get_use_native_tactics      ()      = lookup_opt "use_native_tactics"       (as_option as_string)
let get_use_tactics             ()      = not (lookup_opt "no_tactics"          as_bool)
let get_using_facts_from        ()      = lookup_opt "using_facts_from"         (as_option (as_list as_string))
let get_vcgen_optimize_bind_as_seq  ()  = lookup_opt "vcgen.optimize_bind_as_seq" (as_option as_string)
let get_verify_module           ()      = lookup_opt "verify_module"            (as_list as_string)
let get___temp_no_proj          ()      = lookup_opt "__temp_no_proj"           (as_list as_string)
let get_version                 ()      = lookup_opt "version"                  as_bool
let get_warn_default_effects    ()      = lookup_opt "warn_default_effects"     as_bool
let get_z3cliopt                ()      = lookup_opt "z3cliopt"                 (as_list as_string)
let get_z3refresh               ()      = lookup_opt "z3refresh"                as_bool
let get_z3rlimit                ()      = lookup_opt "z3rlimit"                 as_int
let get_z3rlimit_factor         ()      = lookup_opt "z3rlimit_factor"          as_int
let get_z3seed                  ()      = lookup_opt "z3seed"                   as_int
let get_use_two_phase_tc        ()      = lookup_opt "use_two_phase_tc"         as_bool
let get_no_positivity           ()      = lookup_opt "__no_positivity"          as_bool
let get_ml_no_eta_expand_coertions ()   = lookup_opt "__ml_no_eta_expand_coertions" as_bool
let get_warn_error              ()      = lookup_opt "warn_error"               (as_string)

let dlevel = function
   | "Low" -> Low
   | "Medium" -> Medium
   | "High" -> High
   | "Extreme" -> Extreme
   | s -> Other s
let one_debug_level_geq l1 l2 = match l1 with
   | Other _
   | Low -> l1 = l2
   | Medium -> (l2 = Low || l2 = Medium)
   | High -> (l2 = Low || l2 = Medium || l2 = High)
   | Extreme -> (l2 = Low || l2 = Medium || l2 = High || l2 = Extreme)
let debug_level_geq l2 = get_debug_level() |> Util.for_some (fun l1 -> one_debug_level_geq (dlevel l1) l2)

// Note: the "ulib/fstar" is for the case where package is installed in the
// standard "unix" way (e.g. opam) and the lib directory is $PREFIX/lib/fstar
let universe_include_path_base_dirs =
  ["/ulib"; "/lib/fstar"]

// See comment in the interface file
let _version = FStar.Util.mk_ref ""
let _platform = FStar.Util.mk_ref ""
let _compiler = FStar.Util.mk_ref ""
let _date = FStar.Util.mk_ref ""
let _commit = FStar.Util.mk_ref ""

let display_version () =
  Util.print_string (Util.format5 "F* %s\nplatform=%s\ncompiler=%s\ndate=%s\ncommit=%s\n"
                                  !_version !_platform !_compiler !_date !_commit)

let display_usage_aux specs =
  Util.print_string "fstar.exe [options] file[s]\n";
  List.iter
    (fun (_, flag, p, doc) ->
       match p with
         | ZeroArgs ig ->
             if doc = "" then Util.print_string (Util.format1 "  --%s\n" (Util.colorize_bold flag))
             else Util.print_string (Util.format2 "  --%s  %s\n" (Util.colorize_bold flag) doc)
         | OneArg (_, argname) ->
             if doc = "" then Util.print_string (Util.format2 "  --%s %s\n" (Util.colorize_bold flag) (Util.colorize_bold argname))
             else Util.print_string (Util.format3 "  --%s %s  %s\n" (Util.colorize_bold flag) (Util.colorize_bold argname) doc))
    specs

let mk_spec o : opt =
    let ns, name, arg, desc = o in
    let arg =
        match arg with
        | ZeroArgs f ->
          let g () = set_option name (f()) in
          ZeroArgs g

        | OneArg (f, d) ->
          let g x = set_option name (f x) in
          OneArg (g, d) in
    ns, name, arg, desc

let accumulated_option name value =
    let prev_values = Util.dflt [] (lookup_opt name (as_option as_list')) in
    mk_list (value :: prev_values)

let reverse_accumulated_option name value =
    mk_list ((lookup_opt name as_list') @ [value])

let accumulate_string name post_processor value =
    set_option name (accumulated_option name (mk_string (post_processor value)))

let add_extract_module s =
    accumulate_string "extract_module" String.lowercase s

let add_extract_namespace s =
    accumulate_string "extract_namespace" String.lowercase s

let add_verify_module s =
    accumulate_string "verify_module" String.lowercase s

type opt_type =
| Const of option_val
  // --cache_checked_modules
| IntStr of string (* label *)
  // --z3rlimit 5
| BoolStr
  // --admit_smt_queries true
| PathStr of string (* label *)
  // --fstar_home /build/fstar
| SimpleStr of string (* label *)
  // --admit_except xyz
| EnumStr of list<string>
  // --codegen OCaml
| OpenEnumStr of list<string> (* suggested values (not exhaustive) *) * string (* label *)
  // --debug_level …
| PostProcessed of ((option_val -> option_val) (* validator *) * opt_type (* elem spec *))
  // For options like --extract_module that require post-processing or validation
| Accumulated of opt_type (* elem spec *)
  // For options like --extract_module that can be repeated (LIFO)
| ReverseAccumulated of opt_type (* elem spec *)
  // For options like --include that can be repeated (FIFO)
| WithSideEffect of ((unit -> unit) * opt_type (* elem spec *))
  // For options like --version that have side effects

exception InvalidArgument of string // option name

(** Parse option value `str_val` according to specification `typ`.

For example, to parse the value "OCaml" for the option "--codegen", this
function is called as ``parse_opt_val "codegen" (EnumStr ["OCaml"; "FSharp";
"Kremlin"]) "OCaml"`` and returns ``String "OCaml"``.

`opt_name` is only used in error messages. **)
let rec parse_opt_val (opt_name: string) (typ: opt_type) (str_val: string) : option_val =
  try
    match typ with
    | Const c -> c
    | IntStr _ -> (match safe_int_of_string str_val with
                  | Some v -> mk_int v
                  | None -> raise (InvalidArgument opt_name))
    | BoolStr -> mk_bool (if str_val = "true" then true
                         else if str_val = "false" then false
                         else raise (InvalidArgument opt_name))
    | PathStr _ -> mk_path str_val
    | SimpleStr _ -> mk_string str_val
    | EnumStr strs -> if List.mem str_val strs then mk_string str_val
                     else raise (InvalidArgument opt_name)
    | OpenEnumStr _ -> mk_string str_val
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

let rec desc_of_opt_type typ : option<string> =
  let desc_of_enum cases =
    Some ("[" ^ (String.concat "|" cases) ^ "]") in
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

let rec arg_spec_of_opt_type opt_name typ : opt_variant<option_val> =
  let parser = parse_opt_val opt_name typ in
  match desc_of_opt_type typ with
  | None -> ZeroArgs (fun () -> parser "")
  | Some desc -> OneArg (parser, desc)

let pp_validate_dir p =
  let pp = as_string p in
  mkdir false pp;
  p

let pp_lowercase s =
  mk_string (String.lowercase (as_string s))

let rec specs_with_types () : list<(char * string * opt_type * string)> =
     [( noshort,
        "admit_smt_queries",
        BoolStr,
        "Admit SMT queries, unsafe! (default 'false')");

      ( noshort,
        "admit_except",
        SimpleStr "[symbol|(symbol, id)]",
        "Admit all queries, except those with label (<symbol>, <id>)) (e.g. --admit_except '(FStar.Fin.pigeonhole, 1)' or --admit_except FStar.Fin.pigeonhole)");

      ( noshort,
        "cache_checked_modules",
        Const (mk_bool true),
        "Write a '.checked' file for each module after verification and read from it if present, instead of re-verifying");

      ( noshort,
        "codegen",
        EnumStr ["OCaml"; "FSharp"; "Kremlin"; "tactics"],
        "Generate code for execution");

      ( noshort,
        "codegen-lib",
        Accumulated (SimpleStr "namespace"),
        "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)");

      ( noshort,
        "debug",
        Accumulated (SimpleStr "module_name"),
        "Print lots of debugging information while checking module");

       ( noshort,
        "debug_level",
        Accumulated (OpenEnumStr (["Low"; "Medium"; "High"; "Extreme"], "...")),
        "Control the verbosity of debugging info");

       ( noshort,
        "dep",
        EnumStr ["make"; "graph"; "full"],
        "Output the transitive closure of the full dependency graph in three formats:\n\t \
         'graph': a format suitable the 'dot' tool from 'GraphViz'\n\t \
         'full': a format suitable for 'make', including dependences for producing .ml and .krml files\n\t \
         'make': (deprecated) a format suitable for 'make', including only dependences among source files");

       ( noshort,
        "detail_errors",
        Const (mk_bool true),
         "Emit a detailed error report by asking the SMT solver many queries; will take longer;
         implies n_cores=1");

       ( noshort,
        "detail_hint_replay",
        Const (mk_bool true),
         "Emit a detailed report for proof whose unsat core fails to replay;
         implies n_cores=1");

       ( noshort,
        "doc",
        Const (mk_bool true),
         "Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.");

       ( noshort,
        "dump_module",
        Accumulated (SimpleStr "module_name"),
        "");

       ( noshort,
        "eager_inference",
        Const (mk_bool true),
        "Solve all type-inference constraints eagerly; more efficient but at the cost of generality");

       ( noshort,
         "extract",
         Accumulated (SimpleStr "One or more space-separated occurrences of '[+|-]( * | namespace | module)'"),
        "\n\t\tExtract only those modules whose names or namespaces match the provided options.\n\t\t\t\
         Modules can be extracted or not using the [+|-] qualifier. \n\t\t\t\
         For example --extract '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\t\
         not extract FStar.List.Tot.*, \n\t\t\t\t\
         extract remaining modules from FStar.List.*, \n\t\t\t\t\
         not extract FStar.Reflection.*, \n\t\t\t\t\
         and extract all the rest.\n\t\t\
         Note, the '+' is optional: --extract '+A' and --extract 'A' mean the same thing.\n\t\t\
         Multiple uses of this option accumulate, e.g., --extract A --extract B is interpreted as --extract 'A B'.");

       ( noshort,
        "extract_module",
        Accumulated (PostProcessed (pp_lowercase, (SimpleStr "module_name"))),
        "Deprecated: use --extract instead; Only extract the specified modules (instead of the possibly-partial dependency graph)");

       ( noshort,
        "extract_namespace",
        Accumulated (PostProcessed (pp_lowercase, (SimpleStr "namespace name"))),
        "Deprecated: use --extract instead; Only extract modules in the specified namespace");

       ( noshort,
        "expose_interfaces",
        Const (mk_bool true),
        "Explicitly break the abstraction imposed by the interface of any implementation file that appears on the command line (use with care!)");

       ( noshort,
        "fstar_home",
        PathStr "dir",
        "Set the FSTAR_HOME variable to <dir>");

       ( noshort,
         "gen_native_tactics",
         PathStr "[path]",
        "Compile all user tactics used in the module in <path>");

       ( noshort,
        "hide_uvar_nums",
        Const (mk_bool true),
        "Don't print unification variable numbers");

       ( noshort,
         "hint_file",
         PathStr "path",
        "Read/write hints to <path> (instead of module-specific hints files)");

       ( noshort,
        "hint_info",
        Const (mk_bool true),
        "Print information regarding hints (deprecated; use --query_stats instead)");

       ( noshort,
        "in",
        Const (mk_bool true),
        "Legacy interactive mode; reads input from stdin");

       ( noshort,
        "ide",
        Const (mk_bool true),
        "JSON-based interactive mode for IDEs");

       ( noshort,
        "include",
        ReverseAccumulated (PathStr "path"),
        "A directory in which to search for files included on the command line");

       ( noshort,
        "indent",
        Const (mk_bool true),
        "Parses and outputs the files on the command line");

       ( noshort,
        "initial_fuel",
        IntStr "non-negative integer",
        "Number of unrolling of recursive functions to try initially (default 2)");

       ( noshort,
        "initial_ifuel",
        IntStr "non-negative integer",
        "Number of unrolling of inductive datatypes to try at first (default 1)");

       ( noshort,
        "lax",
        Const (mk_bool true),
        "Run the lax-type checker only (admit all verification conditions)");

      ( noshort,
       "load",
        ReverseAccumulated (PathStr "module"),
        "Load compiled module");

       ( noshort,
        "log_types",
        Const (mk_bool true),
        "Print types computed for data/val/let-bindings");

       ( noshort,
        "log_queries",
        Const (mk_bool true),
        "Log the Z3 queries in several queries-*.smt2 files, as we go");

       ( noshort,
        "max_fuel",
        IntStr "non-negative integer",
        "Number of unrolling of recursive functions to try at most (default 8)");

       ( noshort,
        "max_ifuel",
        IntStr "non-negative integer",
        "Number of unrolling of inductive datatypes to try at most (default 2)");

       ( noshort,
        "min_fuel",
        IntStr "non-negative integer",
        "Minimum number of unrolling of recursive functions to try (default 1)");

       ( noshort,
        "MLish",
        Const (mk_bool true),
        "Trigger various specializations for compiling the F* compiler itself (not meant for user code)");

       ( noshort,
        "n_cores",
        IntStr "positive_integer", //; detail_errors := false),
        "Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)");

       ( noshort,
        "no_default_includes",
        Const (mk_bool true),
        "Ignore the default module search paths");

       ( noshort,
        "no_extract",
        Accumulated (PathStr "module name"),
        "Deprecated: use --extract instead; Do not extract code from this module");

       ( noshort,
        "no_location_info",
        Const (mk_bool true),
        "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)");

       ( noshort,
        "odir",
        PostProcessed (pp_validate_dir, PathStr "dir"),
        "Place output in directory <dir>");

       ( noshort,
        "prims",
        PathStr "file",
        "");

       ( noshort,
        "print_bound_var_types",
        Const (mk_bool true),
        "Print the types of bound variables");

       ( noshort,
        "print_effect_args",
        Const (mk_bool true),
        "Print inferred predicate transformers for all computation types");

       ( noshort,
        "print_full_names",
        Const (mk_bool true),
        "Print full names of variables");

       ( noshort,
        "print_implicits",
        Const (mk_bool true),
        "Print implicit arguments");

       ( noshort,
        "print_universes",
        Const (mk_bool true),
        "Print universes");

       ( noshort,
        "print_z3_statistics",
        Const (mk_bool true),
        "Print Z3 statistics for each SMT query (deprecated; use --query_stats instead)");

       ( noshort,
        "prn",
        Const (mk_bool true),
        "Print full names (deprecated; use --print_full_names instead)");

       ( noshort,
        "query_stats",
        Const (mk_bool true),
        "Print SMT query statistics");

       ( noshort,
        "record_hints",
        Const (mk_bool true),
        "Record a database of hints for efficient proof replay");

       ( noshort,
        "reuse_hint_for",
        SimpleStr "toplevel_name",
        "Optimistically, attempt using the recorded hint for <toplevel_name> (a top-level name in the current module) when trying to verify some other term 'g'");

       ( noshort,
        "silent",
        Const (mk_bool true),
        " ");

       ( noshort,
        "smt",
        PathStr "path",
        "Path to the Z3 SMT solver (we could eventually support other solvers)");

       (noshort,
        "smtencoding.elim_box",
        BoolStr,
        "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')");

       (noshort,
        "smtencoding.nl_arith_repr",
        EnumStr ["native"; "wrapped"; "boxwrap"],
        "Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\t\
         i.e., if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'; \n\t\t\
               if 'native' use '*, div, mod';\n\t\t\
               if 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'; \n\t\t\
               (default 'boxwrap')");

       (noshort,
        "smtencoding.l_arith_repr",
        EnumStr ["native"; "boxwrap"],
        "Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\t\
         i.e., if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'; \n\t\t\
               if 'native', use '+, -, -'; \n\t\t\
               (default 'boxwrap')");

       ( noshort,
        "tactic_raw_binders",
        Const (mk_bool true),
        "Do not use the lexical scope of tactics to improve binder names");

       ( noshort,
        "tactic_trace",
        Const (mk_bool true),
        "Print a depth-indexed trace of tactic execution (Warning: very verbose)");

       ( noshort,
        "tactic_trace_d",
        IntStr "positive_integer",
        "Trace tactics up to a certain binding depth");

       ( noshort,
        "timing",
        Const (mk_bool true),
        "Print the time it takes to verify each top-level definition");

       ( noshort,
        "trace_error",
        Const (mk_bool true),
        "Don't print an error message; show an exception trace instead");

      ( noshort,
        "ugly",
        Const (mk_bool true),
        "Emit output formatted for debugging");

       ( noshort,
        "unthrottle_inductives",
        Const (mk_bool true),
        "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)");

       ( noshort,
        "unsafe_tactic_exec",
        Const (mk_bool true),
        "Allow tactics to run external processes. WARNING: checking an untrusted F* file while \
         using this option can have disastrous effects.");

       ( noshort,
        "use_eq_at_higher_order",
        Const (mk_bool true),
        "Use equality constraints when comparing higher-order types (Temporary)");

       ( noshort,
        "use_hints",
        Const (mk_bool true),
        "Use a previously recorded hints database for proof replay");

       ( noshort,
        "use_hint_hashes",
        Const (mk_bool true),
        "Admit queries if their hash matches the hash recorded in the hints database");

       ( noshort,
         "use_native_tactics",
         PathStr "path",
        "Use compiled tactics from <path>");

       ( noshort,
        "no_tactics",
        Const (mk_bool true),
        "Do not run the tactic engine before discharging a VC");

       ( noshort,
         "using_facts_from",
         Accumulated (SimpleStr "One or more space-separated occurrences of '[+|-]( * | namespace | fact id)'"),
        "\n\t\tPrunes the context to include only the facts from the given namespace or fact id. \n\t\t\t\
         Facts can be include or excluded using the [+|-] qualifier. \n\t\t\t\
         For example --using_facts_from '* -FStar.Reflection +FStar.List -FStar.List.Tot' will \n\t\t\t\t\
         remove all facts from FStar.List.Tot.*, \n\t\t\t\t\
         retain all remaining facts from FStar.List.*, \n\t\t\t\t\
         remove all facts from FStar.Reflection.*, \n\t\t\t\t\
         and retain all the rest.\n\t\t\
         Note, the '+' is optional: --using_facts_from 'FStar.List' is equivalent to --using_facts_from '+FStar.List'. \n\t\t\
         Multiple uses of this option accumulate, e.g., --using_facts_from A --using_facts_from B is interpreted as --using_facts_from A^B.");

       ( noshort,
         "vcgen.optimize_bind_as_seq",
          EnumStr ["off"; "without_type"; "with_type"],
          "\n\t\tOptimize the generation of verification conditions, \n\t\t\t\
           specifically the construction of monadic `bind`,\n\t\t\t\
           generating `seq` instead of `bind` when the first computation as a trivial post-condition.\n\t\t\t\
           By default, this optimization does not apply.\n\t\t\t\
           When the `without_type` option is chosen, this imposes a cost on the SMT solver\n\t\t\t\
           to reconstruct type information.\n\t\t\t\
           When `with_type` is chosen, type information is provided to the SMT solver,\n\t\t\t\
           but at the cost of VC bloat, which may often be redundant.");

       ( noshort,
        "__temp_no_proj",
        Accumulated (SimpleStr "module_name"),
        "Don't generate projectors for this module");

       ( 'v',
         "version",
         WithSideEffect ((fun _ -> display_version(); exit 0),
                         (Const (mk_bool true))),
         "Display version number");

       ( noshort,
         "warn_default_effects",
         Const (mk_bool true),
         "Warn when (a -> b) is desugared to (a -> Tot b)");

       ( noshort,
         "z3cliopt",
         ReverseAccumulated (SimpleStr "option"),
         "Z3 command line options");

       ( noshort,
        "z3refresh",
        Const (mk_bool true),
        "Restart Z3 after each query; useful for ensuring proof robustness");

       ( noshort,
        "z3rlimit",
        IntStr "positive_integer",
        "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)");

       ( noshort,
        "z3rlimit_factor",
        IntStr "positive_integer",
        "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)");

       ( noshort,
        "z3seed",
        IntStr "positive_integer",
        "Set the Z3 random seed (default 0)");

       ( noshort,
        "use_two_phase_tc",
        BoolStr,
        "Use the two phase typechecker (default 'false')");

       ( noshort,
        "__no_positivity",
        Const (mk_bool true),
        "Don't check positivity of inductive types");

       ( noshort,
        "__ml_no_eta_expand_coertions",
        Const (mk_bool true),
        "Do not eta-expand coertions in generated OCaml");

        ( noshort,
        "warn_error",
        SimpleStr (""),
        "The [-warn_error] option follows the OCaml syntax, namely:\n\t\t\
         - [r] is a range of warnings (either a number [n], or a range [n..n])\n\t\t\
         - [-r] silences range [r]\n\t\t\
         - [+r] enables range [r]\n\t\t\
         - [@r] makes range [r] fatal.");

       ('h',
        "help", WithSideEffect ((fun _ -> display_usage_aux (specs ()); exit 0),
                                (Const (mk_bool true))),
        "Display this information")]

and specs () : list<FStar.Getopt.opt> = // FIXME: Why does the interactive mode log the type of opt_specs_with_types as a triple??
  List.map (fun (short, long, typ, doc) ->
            mk_spec (short, long, arg_spec_of_opt_type long typ, doc))
           (specs_with_types ())

//Several options can only be set at the time the process is created, and not controlled interactively via pragmas
//Additionaly, the --smt option is a security concern
let settable = function
    | "admit_smt_queries"
    | "admit_except"
    | "debug"
    | "debug_level"
    | "detail_errors"
    | "detail_hint_replay"
    | "eager_inference"
    | "hide_uvar_nums"
    | "hint_info"
    | "hint_file"
    | "initial_fuel"
    | "initial_ifuel"
    | "lax"
    | "load"
    | "log_types"
    | "log_queries"
    | "max_fuel"
    | "max_ifuel"
    | "min_fuel"
    | "ugly"
    | "print_bound_var_types"
    | "print_effect_args"
    | "print_full_names"
    | "print_implicits"
    | "print_universes"
    | "print_z3_statistics"
    | "prn"
    | "query_stats"
    | "silent"
    | "smtencoding.elim_box"
    | "smtencoding.nl_arith_repr"
    | "smtencoding.l_arith_repr"
    | "timing"
    | "trace_error"
    | "unthrottle_inductives"
    | "use_eq_at_higher_order"
    | "no_tactics"
    | "tactic_raw_binders"
    | "tactic_trace"
    | "tactic_trace_d"
    | "__temp_no_proj"
    | "reuse_hint_for"
    | "warn_error"
    | "z3rlimit_factor"
    | "z3rlimit"
    | "z3refresh"
    | "use_two_phase_tc"
    | "vcgen.optimize_bind_as_seq" -> true
    | _ -> false

// the first two options below are options that are passed to z3 using
// command-line arguments;
// using_facts_from requires pruning the Z3 context.
// All of these can only be used with #reset_options, with re-starts the z3 process
let resettable s = settable s || s="z3seed" || s="z3cliopt" || s="using_facts_from"
let all_specs = specs ()
let all_specs_with_types = specs_with_types ()
let settable_specs = all_specs |> List.filter (fun (_, x, _, _) -> settable x)
let resettable_specs = all_specs |> List.filter (fun (_, x, _, _) -> resettable x)


/////////////////////////////////////////////////////////////////////////////////////////////////////////
//PUBLIC API
/////////////////////////////////////////////////////////////////////////////////////////////////////////
let display_usage () = display_usage_aux (specs())

let fstar_home () =
    match get_fstar_home() with
    | None ->
      let x = Util.get_exec_dir () in
      let x = x ^ "/.." in
      // Memoizes to avoid repeatedly forking an external process
      set_option' ("fstar_home", mk_string x);
      x
    | Some x ->
      x

exception File_argument of string

let set_options o s =
    let specs = match o with
        | Set -> settable_specs
        | Reset -> resettable_specs
        | Restore -> all_specs in
    try
        if s = ""
        then Success
        else Getopt.parse_string specs (fun s -> raise (File_argument s); ()) s
    with
      | File_argument s -> Getopt.Error (FStar.Util.format1 "File %s is not a valid option" s)

let file_list_ : ref<(list<string>)> = Util.mk_ref []

let parse_cmd_line () =
  let res = Getopt.parse_cmdline all_specs (fun i -> file_list_ := !file_list_ @ [i]) in
  res, List.map FC.try_convert_file_name_to_mixed !file_list_

let file_list () =
  !file_list_

let restore_cmd_line_options should_clear =
    (* Some options must be preserved because they can't be reset via #pragrams.
     * Add them here as needed. *)
    let old_verify_module = get_verify_module() in
    if should_clear then clear() else init();
    let r = Getopt.parse_cmdline (specs()) (fun x -> ()) in
    set_option' ("verify_module", List (List.map mk_string old_verify_module));
    r

let module_name_of_file_name f =
    let f = basename f in
    let f = String.substring f 0 (String.length f - String.length (get_file_extension f) - 1) in
    String.lowercase f

let should_verify m =
  if get_lax () then
    false
  else let l = get_verify_module () in
       List.contains (String.lowercase m) l

let should_verify_file fn = should_verify (module_name_of_file_name fn)

let dont_gen_projectors m = List.contains m (get___temp_no_proj())

let should_print_message m =
    if should_verify m
    then m <> "Prims"
    else false

let include_path () =
  if get_no_default_includes() then
    get_include()
  else
    let h = fstar_home () in
    let defs = universe_include_path_base_dirs in
    (defs |> List.map (fun x -> h ^ x) |> List.filter file_exists) @ get_include() @ [ "." ]

let find_file filename =
  if Util.is_path_absolute filename then
    if Util.file_exists filename then
      Some filename
    else
      None
  else
    (* In reverse, because the last directory has the highest precedence. *)
    Util.find_map (List.rev (include_path ())) (fun p ->
      let path = Util.join_paths p filename in
      if Util.file_exists path then
        Some path
      else
        None)

let prims () =
  match get_prims() with
  | None ->
    let filename = "prims.fst" in
    begin match find_file filename with
      | Some result ->
        result
      | None ->
        failwith (Util.format1 "unable to find required file \"%s\" in the module search path.\n" filename)
    end
  | Some x -> x

let prims_basename () = basename (prims ())

let pervasives () =
  let filename = "FStar.Pervasives.fst" in
  match find_file filename with
  | Some result -> result
  | None        -> failwith (Util.format1 "unable to find required file \"%s\" in the module search path.\n" filename)

let pervasives_basename () = basename (pervasives ())
let pervasives_native_basename () =
  let filename = "FStar.Pervasives.Native.fst" in
  match find_file filename with
  | Some result -> basename result
  | None        -> failwith (Util.format1 "unable to find required file \"%s\" in the module search path.\n" filename)


let prepend_output_dir fname =
  match get_odir() with
  | None -> fname
  | Some x -> x ^ "/" ^ fname

//Used to parse the options of
//   --using_facts_from
//   --extract
let parse_settings ns : list<(list<string> * bool)> =
    let parse_one_setting s =
        if s = "*" then ([], true)
        else if FStar.Util.starts_with s "-"
        then let path = FStar.Ident.path_of_text (FStar.Util.substring_from s 1) in
             (path, false)
        else let s = if FStar.Util.starts_with s "+"
                     then FStar.Util.substring_from s 1
                     else s in
             (FStar.Ident.path_of_text s, true)
    in
    ns |> List.collect (fun s ->
          FStar.Util.split s " "
          |> List.map parse_one_setting)
       |> List.rev

let __temp_no_proj               s  = get___temp_no_proj() |> List.contains s
let admit_smt_queries            () = get_admit_smt_queries           ()
let admit_except                 () = get_admit_except                ()
let cache_checked_modules        () = get_cache_checked_modules       ()
let codegen                      () = get_codegen                     ()
let codegen_libs                 () = get_codegen_lib () |> List.map (fun x -> Util.split x ".")
let debug_any                    () = get_debug () <> []
let debug_at_level      modul level = (get_debug () |> List.contains modul) && debug_level_geq level
let dep                          () = get_dep                         ()
let detail_errors                () = get_detail_errors               ()
let detail_hint_replay           () = get_detail_hint_replay          ()
let doc                          () = get_doc                         ()
let dump_module                  s  = get_dump_module() |> List.contains s
let eager_inference              () = get_eager_inference             ()
let expose_interfaces            () = get_expose_interfaces          ()
let fs_typ_app    (filename:string) = List.contains filename !light_off_files
let gen_native_tactics           () = get_gen_native_tactics          ()
let full_context_dependency      () = true
let hide_uvar_nums               () = get_hide_uvar_nums              ()
let hint_info                    () = get_hint_info                   ()
                                    || get_query_stats                 ()
let hint_file                    () = get_hint_file                   ()
let ide                          () = get_ide                         ()
let indent                       () = get_indent                      ()
let initial_fuel                 () = min (get_initial_fuel ()) (get_max_fuel ())
let initial_ifuel                () = min (get_initial_ifuel ()) (get_max_ifuel ())
let interactive                  () = get_in () || get_ide ()
let lax                          () = get_lax                         ()
let load                         () = get_load                        ()
let legacy_interactive           () = get_in                          ()
let log_queries                  () = get_log_queries                 ()
let log_types                    () = get_log_types                   ()
let max_fuel                     () = get_max_fuel                    ()
let max_ifuel                    () = get_max_ifuel                   ()
let min_fuel                     () = get_min_fuel                    ()
let ml_ish                       () = get_MLish                       ()
let set_ml_ish                   () = set_option "MLish" (Bool true)
let n_cores                      () = get_n_cores                     ()
let no_default_includes          () = get_no_default_includes         ()
let no_extract                   s  = let s = String.lowercase s in
    get_no_extract() |> FStar.Util.for_some (fun f -> String.lowercase f = s)
let no_location_info             () = get_no_location_info            ()
let output_dir                   () = get_odir                        ()
let ugly                         () = get_ugly                        ()
let print_bound_var_types        () = get_print_bound_var_types       ()
let print_effect_args            () = get_print_effect_args           ()
let print_implicits              () = get_print_implicits             ()
let print_real_names             () = get_prn () || get_print_full_names()
let print_universes              () = get_print_universes             ()
let print_z3_statistics          () = get_print_z3_statistics         ()
                                    || get_query_stats                ()
let query_stats                  () = get_query_stats                 ()
let record_hints                 () = get_record_hints                ()
let reuse_hint_for               () = get_reuse_hint_for              ()
let silent                       () = get_silent                      ()
let smtencoding_elim_box         () = get_smtencoding_elim_box        ()
let smtencoding_nl_arith_native  () = get_smtencoding_nl_arith_repr () = "native"
let smtencoding_nl_arith_wrapped () = get_smtencoding_nl_arith_repr () = "wrapped"
let smtencoding_nl_arith_default () = get_smtencoding_nl_arith_repr () = "boxwrap"
let smtencoding_l_arith_native   () = get_smtencoding_l_arith_repr () = "native"
let smtencoding_l_arith_default  () = get_smtencoding_l_arith_repr () = "boxwrap"
let tactic_raw_binders           () = get_tactic_raw_binders          ()
let tactic_trace                 () = get_tactic_trace                ()
let tactic_trace_d               () = get_tactic_trace_d              ()
let timing                       () = get_timing                      ()
let trace_error                  () = get_trace_error                 ()
let unthrottle_inductives        () = get_unthrottle_inductives       ()
let unsafe_tactic_exec           () = get_unsafe_tactic_exec          ()
let use_eq_at_higher_order       () = get_use_eq_at_higher_order      ()
let use_hints                    () = get_use_hints                   ()
let use_hint_hashes              () = get_use_hint_hashes             ()
let use_native_tactics           () = get_use_native_tactics          ()
let use_tactics                  () = get_use_tactics                 ()
let using_facts_from             () =
    match get_using_facts_from () with
    | None -> [ [], true ] //if not set, then retain all facts
    | Some ns -> parse_settings ns
let vcgen_optimize_bind_as_seq   () = Option.isSome (get_vcgen_optimize_bind_as_seq  ())
let vcgen_decorate_with_type     () = match get_vcgen_optimize_bind_as_seq  () with
                                      | Some "with_type" -> true
                                      | _ -> false
let warn_default_effects         () = get_warn_default_effects        ()
let z3_exe                       () = match get_smt () with
                                    | None -> Platform.exe "z3"
                                    | Some s -> s
let z3_cliopt                    () = get_z3cliopt                    ()
let z3_refresh                   () = get_z3refresh                   ()
let z3_rlimit                    () = get_z3rlimit                    ()
let z3_rlimit_factor             () = get_z3rlimit_factor             ()
let z3_seed                      () = get_z3seed                      ()
let use_two_phase_tc             () = get_use_two_phase_tc            ()
let no_positivity                () = get_no_positivity               ()
let ml_no_eta_expand_coertions   () = get_ml_no_eta_expand_coertions  ()
let warn_error                   () = get_warn_error                  ()

let should_extract m =
    let m = String.lowercase m in
    match get_extract() with
    | Some extract_setting -> //new option, using --extract '* -FStar' etc.
      let _ = match get_no_extract(), get_extract_namespace(), get_extract_module () with
              | [], [], [] -> ()
              | _ -> failwith "Incompatible options: --extract cannot be used with --no_extract, --extract_namespace or --extract_module"
      in
      let setting = parse_settings extract_setting in
      let m_components = Ident.path_of_text m in
      let rec matches_path m_components path =
          match m_components, path with
          | _, [] -> true
          | m::ms, p::ps -> m=String.lowercase p && matches_path ms ps
          | _ -> false
      in
      begin
      match setting |> Util.try_find (fun (path, _) -> matches_path m_components path) with
      | None -> false
      | Some (_, flag) -> flag
      end
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
        | [], [] -> true //neither is set
        | _ -> should_extract_namespace m || should_extract_module m)

let codegen_fsharp () =
    codegen() = Some "FSharp"

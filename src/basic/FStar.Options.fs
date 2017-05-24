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
open FStar.All
open FStar
open FStar.Util
open FStar.Getopt

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
let as_list as_t = function
  | List ts -> ts |> List.map as_t
  | _ -> failwith "Impos: expected List"
let as_option as_t = function
  | Unset -> None
  | v -> Some (as_t v)

let fstar_options : ref<list<Util.smap<option_val>> > = Util.mk_ref []
let peek () = List.hd !fstar_options
let pop  () =
    match !fstar_options with
    | []
    | [_] -> failwith "TOO MANY POPS!"
    | _::tl -> fstar_options := tl
let push () = fstar_options := Util.smap_copy (peek()) :: !fstar_options
let set_option k v = Util.smap_add (peek()) k v
let set_option' (k,v) =  set_option k v

let with_saved_options f =
  push (); let retv = f () in pop (); retv

let light_off_files : ref<list<string>> = Util.mk_ref []
let add_light_off_file (filename:string) = light_off_files := filename :: !light_off_files

let defaults =
     [
      ("__temp_no_proj"               , List []);
      ("_fstar_home"                  , String "");
      ("_include_path"                , List []);
      ("admit_smt_queries"            , Bool false);
      ("check_hints"                  , Bool false);
      ("codegen"                      , Unset);
      ("codegen-lib"                  , List []);
      ("debug"                        , List []);
      ("debug_level"                  , List []);
      ("dep"                          , Unset);
      ("detail_errors"                , Bool false);
      ("doc"                          , Bool false);
      ("dump_module"                  , List []);
      ("eager_inference"              , Bool false);
      ("explicit_deps"                , Bool false);
      ("extract_all"                  , Bool false);
      ("extract_module"               , List []);
      ("extract_namespace"            , List []);
      ("fs_typ_app"                   , Bool false);
      ("fstar_home"                   , Unset);
      ("full_context_dependency"      , Bool true);
      ("hide_genident_nums"           , Bool false);
      ("hide_uvar_nums"               , Bool false);
      ("hint_info"                    , Bool false);
      ("in"                           , Bool false);
      ("ide"                          , Bool false);
      ("include"                      , List []);
      ("indent"                       , Bool false);
      ("initial_fuel"                 , Int 2);
      ("initial_ifuel"                , Int 1);
      ("lax"                          , Bool false);
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
      ("odir"                         , Unset);
      ("prims"                        , Unset);
      ("pretype"                      , Bool true);
      ("prims_ref"                    , Unset);
      ("print_before_norm"            , Bool false);
      ("print_bound_var_types"        , Bool false);
      ("print_effect_args"            , Bool false);
      ("print_fuels"                  , Bool false);
      ("print_full_names"             , Bool false);
      ("print_implicits"              , Bool false);
      ("print_universes"              , Bool false);
      ("print_z3_statistics"          , Bool false);
      ("prn"                          , Bool false);
      ("record_hints"                 , Bool false);
      ("reuse_hint_for"               , Unset);
      ("show_signatures"              , List []);
      ("silent"                       , Bool false);
      ("smt"                          , Unset);
      ("smtencoding.elim_box"         , Bool false);
      ("smtencoding.nl_arith_repr"    , String "boxwrap");
      ("smtencoding.l_arith_repr"     , String "boxwrap");
      ("split_cases"                  , Int 0);
      ("timing"                       , Bool false);
      ("trace_error"                  , Bool false);
      ("ugly"                         , Bool false);
      ("unthrottle_inductives"        , Bool false);
      ("use_eq_at_higher_order"       , Bool false);
      ("use_hints"                    , Bool false);
      ("no_tactics"                   , Bool false);
      ("using_facts_from"             , Unset);
      ("verify"                       , Bool true);
      ("verify_all"                   , Bool false);
      ("verify_module"                , List []);
      ("warn_default_effects"         , Bool false);
      ("z3refresh"                    , Bool false);
      ("z3rlimit"                     , Int 5);
      ("z3rlimit_factor"              , Int 1);
      ("z3seed"                       , Int 0);
      ("z3timeout"                    , Int 5);
      ("z3cliopt"                     , List []);
      ("__no_positivity"              , Bool false)]

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
let get_check_hints             ()      = lookup_opt "check_hints"              as_bool
let get_codegen                 ()      = lookup_opt "codegen"                  (as_option as_string)
let get_codegen_lib             ()      = lookup_opt "codegen-lib"              (as_list as_string)
let get_debug                   ()      = lookup_opt "debug"                    (as_list as_string)
let get_debug_level             ()      = lookup_opt "debug_level"              (as_list as_string)
let get_dep                     ()      = lookup_opt "dep"                      (as_option as_string)
let get_detail_errors           ()      = lookup_opt "detail_errors"            as_bool
let get_doc                     ()      = lookup_opt "doc"                      as_bool
let get_dump_module             ()      = lookup_opt "dump_module"              (as_list as_string)
let get_eager_inference         ()      = lookup_opt "eager_inference"          as_bool
let get_explicit_deps           ()      = lookup_opt "explicit_deps"            as_bool
let get_extract_all             ()      = lookup_opt "extract_all"              as_bool
let get_extract_module          ()      = lookup_opt "extract_module"           (as_list as_string)
let get_extract_namespace       ()      = lookup_opt "extract_namespace"        (as_list as_string)
let get_fs_typ_app              ()      = lookup_opt "fs_typ_app"               as_bool
let get_fstar_home              ()      = lookup_opt "fstar_home"               (as_option as_string)
let get_hide_genident_nums      ()      = lookup_opt "hide_genident_nums"       as_bool
let get_hide_uvar_nums          ()      = lookup_opt "hide_uvar_nums"           as_bool
let get_hint_info               ()      = lookup_opt "hint_info"                as_bool
let get_in                      ()      = lookup_opt "in"                       as_bool
let get_ide                     ()      = lookup_opt "ide"                      as_bool
let get_include                 ()      = lookup_opt "include"                  (as_list as_string)
let get_indent                  ()      = lookup_opt "indent"                   as_bool
let get_initial_fuel            ()      = lookup_opt "initial_fuel"             as_int
let get_initial_ifuel           ()      = lookup_opt "initial_ifuel"            as_int
let get_lax                     ()      = lookup_opt "lax"                      as_bool
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
let get_print_before_norm       ()      = lookup_opt "print_before_norm"        as_bool
let get_print_bound_var_types   ()      = lookup_opt "print_bound_var_types"    as_bool
let get_print_effect_args       ()      = lookup_opt "print_effect_args"        as_bool
let get_print_fuels             ()      = lookup_opt "print_fuels"              as_bool
let get_print_full_names        ()      = lookup_opt "print_full_names"         as_bool
let get_print_implicits         ()      = lookup_opt "print_implicits"          as_bool
let get_print_universes         ()      = lookup_opt "print_universes"          as_bool
let get_print_z3_statistics     ()      = lookup_opt "print_z3_statistics"      as_bool
let get_prn                     ()      = lookup_opt "prn"                      as_bool
let get_record_hints            ()      = lookup_opt "record_hints"             as_bool
let get_reuse_hint_for          ()      = lookup_opt "reuse_hint_for"           (as_option as_string)
let get_show_signatures         ()      = lookup_opt "show_signatures"          (as_list as_string)
let get_silent                  ()      = lookup_opt "silent"                   as_bool
let get_smt                     ()      = lookup_opt "smt"                      (as_option as_string)
let get_smtencoding_elim_box    ()      = lookup_opt "smtencoding.elim_box"     as_bool
let get_smtencoding_nl_arith_repr ()    = lookup_opt "smtencoding.nl_arith_repr" as_string
let get_smtencoding_l_arith_repr()      = lookup_opt "smtencoding.l_arith_repr" as_string
let get_split_cases             ()      = lookup_opt "split_cases"              as_int
let get_timing                  ()      = lookup_opt "timing"                   as_bool
let get_trace_error             ()      = lookup_opt "trace_error"              as_bool
let get_unthrottle_inductives   ()      = lookup_opt "unthrottle_inductives"    as_bool
let get_use_eq_at_higher_order  ()      = lookup_opt "use_eq_at_higher_order"   as_bool
let get_use_hints               ()      = lookup_opt "use_hints"                as_bool
let get_use_tactics             ()      = not (lookup_opt "no_tactics"          as_bool)
let get_using_facts_from        ()      = lookup_opt "using_facts_from"         (as_option (as_list as_string))
let get_verify_all              ()      = lookup_opt "verify_all"               as_bool
let get_verify_module           ()      = lookup_opt "verify_module"            (as_list as_string)
let get___temp_no_proj          ()      = lookup_opt "__temp_no_proj"           (as_list as_string)
let get_version                 ()      = lookup_opt "version"                  as_bool
let get_warn_default_effects    ()      = lookup_opt "warn_default_effects"     as_bool
let get_z3cliopt                ()      = lookup_opt "z3cliopt"                 (as_list as_string)
let get_z3refresh               ()      = lookup_opt "z3refresh"                as_bool
let get_z3rlimit                ()      = lookup_opt "z3rlimit"                 as_int
let get_z3rlimit_factor         ()      = lookup_opt "z3rlimit_factor"          as_int
let get_z3seed                  ()      = lookup_opt "z3seed"                   as_int
let get_z3timeout               ()      = lookup_opt "z3timeout"                as_int
let get_no_positivity           ()      = lookup_opt "__no_positivity"          as_bool

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
          let g () = set_option' (name, f()) in
          ZeroArgs g

        | OneArg (f, d) ->
          let g x = set_option' (name, f x) in
          OneArg (g, d) in
    ns, name, arg, desc

let cons_extract_module s  =
    List (String.lowercase s::get_extract_module() |> List.map String)

let cons_extract_namespace s  =
    List (String.lowercase s::get_extract_namespace() |> List.map String)

let add_extract_module s =
    set_option "extract_module" (cons_extract_module s)

let add_extract_namespace s =
    set_option "extract_namespace" (cons_extract_namespace s)

let cons_verify_module s  =
    List (String.lowercase s::get_verify_module() |> List.map String)

let cons_using_facts_from s =
    set_option "z3refresh" (Bool true);
    match get_using_facts_from() with
    | None -> List [String s]
    | Some l -> List (List.map String (s :: l))

let add_verify_module s =
    set_option "verify_module" (cons_verify_module s)


let rec specs () : list<Getopt.opt> =
  let specs =
    [  ( noshort,
       "admit_smt_queries",
       OneArg ((fun s -> if s="true" then Bool true
                         else if s="false" then Bool false
                         else failwith("Invalid argument to --admit_smt_queries")),
                "[true|false]"),
       "Admit SMT queries, unsafe! (default 'false')");

      ( noshort,
       "codegen",
        OneArg ((fun s -> String (parse_codegen s)),
                 "[OCaml|FSharp|Kremlin]"),
        "Generate code for execution");

      ( noshort,
        "codegen-lib",
        OneArg ((fun s -> List (s::get_codegen_lib() |> List.map String)),
                 "[namespace]"),
        "External runtime library (i.e. M.N.x extracts to M.N.X instead of M_N.x)");

      ( noshort,
        "debug",
        OneArg ((fun x -> List (x::get_debug() |> List.map String)),
                 "[module name]"),
        "Print lots of debugging information while checking module");

       ( noshort,
        "debug_level",
        OneArg ((fun x -> List (x::get_debug_level() |> List.map String)),
                 "[Low|Medium|High|Extreme|...]"),
        "Control the verbosity of debugging info");

       ( noshort,
        "dep",
        OneArg ((fun x -> if x = "make" || x = "graph" then String x else failwith "invalid argument to 'dep'"),
                 "[make|graph]"),
        "Output the transitive closure of the dependency graph in a format suitable for the given tool");

       ( noshort,
        "detail_errors",
        ZeroArgs (fun () -> Bool true),
         "Emit a detailed error report by asking the SMT solver many queries; will take longer;
         implies n_cores=1");

       ( noshort,
        "doc",
        ZeroArgs (fun () -> Bool true),
         "Extract Markdown documentation files for the input modules, as well as an index. Output is written to --odir directory.");

       ( noshort,
        "dump_module",
        OneArg ((fun x -> (x::get_dump_module()) |> List.map String |> List),
                 "[module name]"),
        "");

       ( noshort,
        "eager_inference",
        ZeroArgs (fun () -> Bool true),
        "Solve all type-inference constraints eagerly; more efficient but at the cost of generality");

       ( noshort,
        "explicit_deps",
        ZeroArgs (fun () -> Bool true),
        "Do not find dependencies automatically, the user provides them on the command-line");

       ( noshort,
        "extract_all",
        ZeroArgs (fun () -> Bool true),
        "Discover the complete dependency graph and do not stop at interface boundaries");

       ( noshort,
        "extract_module",
        OneArg (cons_extract_module,
                 "[module name]"),
        "Only extract the specified modules (instead of the possibly-partial dependency graph)");

       ( noshort,
        "extract_namespace",
        OneArg (cons_extract_namespace,
                 "[namespace name]"),
        "Only extract modules in the specified namespace");

       ( noshort,
        "fstar_home",
        OneArg (Path,
                "[dir]"),
        "Set the FSTAR_HOME variable to [dir]");

       ( noshort,
        "hide_genident_nums",
        ZeroArgs(fun () -> Bool true),
        "Don't print generated identifier numbers");

       ( noshort,
        "hide_uvar_nums",
        ZeroArgs(fun () -> Bool true),
        "Don't print unification variable numbers");

       ( noshort,
        "hint_info",
        ZeroArgs(fun () -> Bool true),
        "Print information regarding hints");

       ( noshort,
        "in",
        ZeroArgs (fun () -> Bool true),
        "Legacy interactive mode; reads input from stdin");

       ( noshort,
        "ide",
        ZeroArgs (fun () -> Bool true),
        "JSON-based interactive mode for IDEs");

       ( noshort,
        "include",
        OneArg ((fun s -> List (List.map String (get_include()) @ [Path s])),
                "[path]"),
        "A directory in which to search for files included on the command line");

       ( noshort,
        "indent",
        ZeroArgs (fun () -> Bool true),
        "Parses and outputs the files on the command line");

       ( noshort,
        "initial_fuel",
        OneArg((fun x -> Int (int_of_string x)),
                "[non-negative integer]"),
        "Number of unrolling of recursive functions to try initially (default 2)");

       ( noshort,
        "initial_ifuel",
        OneArg((fun x -> Int (int_of_string x)),
                "[non-negative integer]"),
        "Number of unrolling of inductive datatypes to try at first (default 1)");

       ( noshort,
        "inline_arith",
        ZeroArgs(fun () -> Bool true),
        "Inline definitions of arithmetic functions in the SMT encoding");

       ( noshort,
        "lax",
        ZeroArgs (fun () -> Bool true), //pretype := true; verify := false),
        "Run the lax-type checker only (admit all verification conditions)");

       ( noshort,
        "log_types",
        ZeroArgs (fun () -> Bool true),
        "Print types computed for data/val/let-bindings");

       ( noshort,
        "log_queries",
        ZeroArgs (fun () -> Bool true),
        "Log the Z3 queries in several queries-*.smt2 files, as we go");

       ( noshort,
        "max_fuel",
        OneArg((fun x -> Int (int_of_string x)),
                "[non-negative integer]"),
        "Number of unrolling of recursive functions to try at most (default 8)");

       ( noshort,
        "max_ifuel",
        OneArg((fun x -> Int (int_of_string x)),
                "[non-negative integer]"),
        "Number of unrolling of inductive datatypes to try at most (default 2)");

       ( noshort,
        "min_fuel",
        OneArg((fun x -> Int (int_of_string x)),
                "[non-negative integer]"),
        "Minimum number of unrolling of recursive functions to try (default 1)");

       ( noshort,
        "MLish",
        ZeroArgs(fun () -> Bool true),
        "Trigger various specializations for compiling the F* compiler itself (not meant for user code)");

       ( noshort,
        "n_cores",
        OneArg ((fun x -> Int (int_of_string x)),//; detail_errors := false),
                 "[positive integer]"),
        "Maximum number of cores to use for the solver (implies detail_errors = false) (default 1)");

       ( noshort,
        "no_default_includes",
        ZeroArgs (fun () -> Bool true),
        "Ignore the default module search paths");

       ( noshort,
        "no_extract",
        OneArg ((fun x -> List (x :: get_no_extract() |> List.map String)),
                 "[module name]"),
        "Do not extract code from this module");

       ( noshort,
        "no_location_info",
        ZeroArgs (fun () -> Bool true),
        "Suppress location information in the generated OCaml output (only relevant with --codegen OCaml)");

       ( noshort,
        "odir",
        OneArg ((fun p -> Path (validate_dir p)),
                "[dir]"),
        "Place output in directory [dir]");

       ( noshort,
        "prims",
        OneArg (String,
                "file"),
        "");

       ( noshort,
        "print_before_norm",
        ZeroArgs(fun () -> Bool true), // norm_then_print := false),
        "Do not normalize types before printing (for debugging)");

       ( noshort,
        "print_bound_var_types",
        ZeroArgs(fun () -> Bool true),
        "Print the types of bound variables");

       ( noshort,
        "print_effect_args",
        ZeroArgs (fun () -> Bool true),
        "Print inferred predicate transformers for all computation types");

       ( noshort,
        "print_fuels",
        ZeroArgs (fun () -> Bool true),
        "Print the fuel amounts used for each successful query");

       ( noshort,
        "print_full_names",
        ZeroArgs (fun () -> Bool true),
        "Print full names of variables");

       ( noshort,
        "print_implicits",
        ZeroArgs(fun () -> Bool true),
        "Print implicit arguments");

       ( noshort,
        "print_universes",
        ZeroArgs(fun () -> Bool true),
        "Print universes");

       ( noshort,
        "print_z3_statistics",
        ZeroArgs(fun () -> Bool true),
        "Print Z3 statistics for each SMT query");

       ( noshort,
        "prn",
        ZeroArgs (fun () -> Bool true),
        "Print full names (deprecated; use --print_full_names instead)");

       ( noshort,
        "record_hints",
        ZeroArgs (fun () -> Bool true),
        "Record a database of hints for efficient proof replay");

       ( noshort,
        "check_hints",
        ZeroArgs (fun () -> Bool true),
        "Check new hints for replayability");

       ( noshort,
        "reuse_hint_for",
        OneArg (String, "top-level name in the current module"),
        "Optimistically, attempt using the recorded hint for 'f' when trying to verify some other term 'g'");

       ( noshort,
        "show_signatures",
        OneArg((fun x -> List (x::get_show_signatures() |> List.map String)),
                "[module name]"),
        "Show the checked signatures for all top-level symbols in the module");

       ( noshort,
        "silent",
        ZeroArgs (fun () -> Bool true),
        " ");

       ( noshort,
        "smt",
        OneArg (Path,
                 "[path]"),
        "Path to the SMT solver (usually Z3, but could be any SMT2-compatible solver)");

       (noshort,
        "smtencoding.elim_box",
        OneArg (string_as_bool "smtencoding.elim_box",
                "true|false"),
        "Toggle a peephole optimization that eliminates redundant uses of boxing/unboxing in the SMT encoding (default 'false')");

       (noshort,
        "smtencoding.nl_arith_repr",
        OneArg (String,
                "native|wrapped|boxwrap"),
        "Control the representation of non-linear arithmetic functions in the SMT encoding:\n\t\t\
         i.e., if 'boxwrap' use 'Prims.op_Multiply, Prims.op_Division, Prims.op_Modulus'; \n\t\t\
               if 'native' use '*, div, mod';\n\t\t\
               if 'wrapped' use '_mul, _div, _mod : Int*Int -> Int'; \n\t\t\
               (default 'boxwrap')");

       (noshort,
        "smtencoding.l_arith_repr",
        OneArg (String,
                "native|boxwrap"),
        "Toggle the representation of linear arithmetic functions in the SMT encoding:\n\t\t\
         i.e., if 'boxwrap', use 'Prims.op_Addition, Prims.op_Subtraction, Prims.op_Minus'; \n\t\t\
               if 'native', use '+, -, -'; \n\t\t\
               (default 'boxwrap')");

       ( noshort,
        "split_cases",
        OneArg ((fun n -> Int (int_of_string n)),
                 "[positive integer]"),
        "Partition VC of a match into groups of [n] cases");

       ( noshort,
        "timing",
        ZeroArgs (fun () -> Bool true),
        "Print the time it takes to verify each top-level definition");

       ( noshort,
        "trace_error",
        ZeroArgs (fun () -> Bool true),
        "Don't print an error message; show an exception trace instead");

      ( noshort,
        "ugly",
        ZeroArgs (fun () -> Bool true),
        "Emit output formatted for debugging");

       ( noshort,
        "unthrottle_inductives",
        ZeroArgs (fun () -> Bool true),
        "Let the SMT solver unfold inductive types to arbitrary depths (may affect verifier performance)");

       ( noshort,
        "use_eq_at_higher_order",
        ZeroArgs (fun () -> Bool true),
        "Use equality constraints when comparing higher-order types (Temporary)");

       ( noshort,
        "use_hints",
        ZeroArgs (fun () -> Bool true),
        "Use a previously recorded hints database for proof replay");

       ( noshort,
        "no_tactics",
        ZeroArgs (fun () -> Bool true),
        "Do not run the tactic engine before discharging a VC");

       ( noshort,
        "using_facts_from",
        OneArg (cons_using_facts_from, "[namespace | fact id]"),
        "Implies --z3refresh; prunes the context to include facts from the given namespace of fact id \
         (multiple uses of this option will prune the context to include those \
         facts that match any of the provided namespaces / fact ids");

       ( noshort,
        "verify_all",
        ZeroArgs (fun () -> Bool true),
        "With automatic dependencies, verify all the dependencies, not just the files passed on the command-line.");

       ( noshort,
        "verify_module",
        OneArg (cons_verify_module,
                 "[module name]"),
        "Name of the module to verify");

       ( noshort,
        "__temp_no_proj",
         OneArg ((fun x -> List (x :: get___temp_no_proj() |> List.map String)),
                  "[module name]"),
        "Don't generate projectors for this module");

       ( 'v',
         "version",
         ZeroArgs (fun _ -> display_version(); exit 0),
         "Display version number");

       ( noshort,
         "warn_default_effects",
         ZeroArgs (fun _ -> Bool true),
         "Warn when (a -> b) is desugared to (a -> Tot b)");

       ( noshort,
         "z3cliopt",
         OneArg ((fun s -> List (get_z3cliopt() @ [s] |> List.map String)), "[option]"),
         "Z3 command line options");

       ( noshort,
        "z3refresh",
        ZeroArgs (fun () -> Bool true),
        "Restart Z3 after each query; useful for ensuring proof robustness");

       ( noshort,
        "z3rlimit",
         OneArg ((fun s -> Int (int_of_string s)),
                  "[positive integer]"),
        "Set the Z3 per-query resource limit (default 5 units, taking roughtly 5s)");

       ( noshort,
        "z3rlimit_factor",
         OneArg ((fun s -> Int (int_of_string s)),
                  "[positive integer]"),
        "Set the Z3 per-query resource limit multiplier. This is useful when, say, regenerating hints and you want to be more lax. (default 1)");

       ( noshort,
        "z3seed",
         OneArg ((fun s -> Int (int_of_string s)),
                  "[positive integer]"),
        "Set the Z3 random seed (default 0)");

       ( noshort,
        "z3timeout",
         OneArg ((fun s -> Util.print_string "Warning: z3timeout ignored; use z3rlimit instead\n"; Int (int_of_string s)),
                  "[positive integer]"),
        "Set the Z3 per-query (soft) timeout to [t] seconds (default 5)");

       ( noshort,
        "__no_positivity",
        ZeroArgs (fun () -> Bool true),
        "Don't check positivity of inductive types");


  ] in
     ( 'h',
        "help",
        ZeroArgs (fun x -> display_usage_aux specs; exit 0),
        "Display this information")::List.map mk_spec specs

and parse_codegen s =
  match s with
  | "Kremlin"
  | "OCaml"
  | "FSharp" -> s
  | _ ->
     (Util.print_string "Wrong argument to codegen flag\n";
      display_usage_aux (specs ()); exit 1)

and string_as_bool option_name = function
    | "true" -> Bool true
    | "false" -> Bool false
    | _ ->
      Util.print1 "Wrong argument to %s\n" option_name;
      display_usage_aux (specs ()); exit 1

and validate_dir p =
  mkdir false p;
  p

let docs () =
  List.map (fun (_, name, _, doc) -> (name, doc)) (specs ())

//Several options can only be set at the time the process is created, and not controlled interactively via pragmas
//Additionaly, the --smt option is a security concern
let settable = function
    | "admit_smt_queries"
    | "debug"
    | "debug_level"
    | "detail_errors"
    | "eager_inference"
    | "hide_genident_nums"
    | "hide_uvar_nums"
    | "hint_info"
    | "initial_fuel"
    | "initial_ifuel"
    | "inline_arith"
    | "lax"
    | "log_types"
    | "log_queries"
    | "max_fuel"
    | "max_ifuel"
    | "min_fuel"
    | "ugly"
    | "print_before_norm"
    | "print_bound_var_types"
    | "print_effect_args"
    | "print_fuels"
    | "print_full_names"
    | "print_implicits"
    | "print_universes"
    | "print_z3_statistics"
    | "prn"
    | "show_signatures"
    | "silent"
    | "smtencoding.elim_box"
    | "smtencoding.nl_arith_repr"
    | "smtencoding.l_arith_repr"
    | "split_cases"
    | "timing"
    | "trace_error"
    | "unthrottle_inductives"
    | "use_eq_at_higher_order"
    | "no_tactics"
    | "using_facts_from"
    | "__temp_no_proj"
    | "reuse_hint_for"
    | "z3rlimit_factor"
    | "z3rlimit"
    | "z3refresh" -> true
    | _ -> false

// JP: the two options below are options that are passed to z3 using
// command-line arguments; only #reset_options re-starts the z3 process, meaning
// these two options are resettable, but not settable
let resettable s = settable s || s="z3timeout" || s="z3seed" || s="z3cliopt"
let all_specs = specs ()
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
      set_option' ("fstar_home", String x);
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
  let res = Getopt.parse_cmdline (specs()) (fun i -> file_list_ := !file_list_ @ [i]) in
  res, List.map FC.try_convert_file_name_to_mixed !file_list_

let file_list () =
  !file_list_

let restore_cmd_line_options should_clear =
    (* Some options must be preserved because they can't be reset via #pragrams.
     * Add them here as needed. *)
    let old_verify_module = get_verify_module() in
    if should_clear then clear() else init();
    let r = Getopt.parse_cmdline (specs()) (fun x -> ()) in
    set_option' ("verify_module", List (List.map String old_verify_module));
    r

let should_verify m =
  if get_lax () then
    false
  else if get_verify_all () then
    true
  else match get_verify_module () with
    | [] ->
        (* Note: in auto-deps mode, [dep.fs] fills in the [verify_module] option
         * meaning that this case is only called when in [--explicit_deps] mode.
         * If we could remove [--explicit_deps], there would be less complexity
         * here. *)
        List.existsML (fun f ->
          let f = basename f in
          let f = String.substring f 0 (String.length f - String.length (get_file_extension f) - 1) in
          String.lowercase f = m
        ) (file_list ())
    | l ->
        List.contains (String.lowercase m) l

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
            raise (Util.Failure (Util.format1 "unable to find required file \"%s\" in the module search path.\n" filename))
    end
  | Some x -> x

let prims_basename () = basename (prims ())

let pervasives () =
  let filename = "FStar.Pervasives.fst" in
  match find_file filename with
  | Some result -> result
  | None        -> raise (Util.Failure (Util.format1 "unable to find required file \"%s\" in the module search path.\n" filename))

let pervasives_basename () = basename (pervasives ())

let prepend_output_dir fname =
  match get_odir() with
  | None -> fname
  | Some x -> x ^ "/" ^ fname


let __temp_no_proj               s  = get___temp_no_proj() |> List.contains s
let admit_smt_queries            () = get_admit_smt_queries           ()
let check_hints                  () = get_check_hints                 ()
let codegen                      () = get_codegen                     ()
let codegen_libs                 () = get_codegen_lib () |> List.map (fun x -> Util.split x ".")
let debug_any                    () = get_debug () <> []
let debug_at_level      modul level = (modul = "" || get_debug () |> List.contains modul) && debug_level_geq level
let dep                          () = get_dep                         ()
let detail_errors                () = get_detail_errors               ()
let doc                          () = get_doc                         ()
let dump_module                  s  = get_dump_module() |> List.contains s
let eager_inference              () = get_eager_inference             ()
let explicit_deps                () = get_explicit_deps               ()
let extract_all                  () = get_extract_all                 ()
let fs_typ_app    (filename:string) = List.contains filename !light_off_files
let full_context_dependency      () = true
let hide_genident_nums           () = get_hide_genident_nums          ()
let hide_uvar_nums               () = get_hide_uvar_nums              ()
let hint_info                    () = get_hint_info                   ()
let ide                          () = get_ide                         ()
let indent                       () = get_indent                      ()
let initial_fuel                 () = min (get_initial_fuel ()) (get_max_fuel ())
let initial_ifuel                () = min (get_initial_ifuel ()) (get_max_ifuel ())
let interactive                  () = get_in () || get_ide ()
let lax                          () = get_lax                         ()
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
let no_extract                   s  = get_no_extract() |> List.contains s
let no_location_info             () = get_no_location_info            ()
let norm_then_print              () = get_print_before_norm()=false
let output_dir                   () = get_odir                        ()
let ugly                         () = get_ugly                        ()
let print_bound_var_types        () = get_print_bound_var_types       ()
let print_effect_args            () = get_print_effect_args           ()
let print_fuels                  () = get_print_fuels                 ()
let print_implicits              () = get_print_implicits             ()
let print_real_names             () = get_prn () || get_print_full_names()
let print_universes              () = get_print_universes             ()
let print_z3_statistics          () = get_print_z3_statistics         ()
let record_hints                 () = get_record_hints                ()
let reuse_hint_for               () = get_reuse_hint_for              ()
let silent                       () = get_silent                      ()
let smtencoding_elim_box         () = get_smtencoding_elim_box        ()
let smtencoding_nl_arith_native  () = get_smtencoding_nl_arith_repr () = "native"
let smtencoding_nl_arith_wrapped () = get_smtencoding_nl_arith_repr () = "wrapped"
let smtencoding_nl_arith_default () = get_smtencoding_nl_arith_repr () = "boxwrap"
let smtencoding_l_arith_native   () = get_smtencoding_l_arith_repr () = "native"
let smtencoding_l_arith_default  () = get_smtencoding_l_arith_repr () = "boxwrap"
let split_cases                  () = get_split_cases                 ()
let timing                       () = get_timing                      ()
let trace_error                  () = get_trace_error                 ()
let unthrottle_inductives        () = get_unthrottle_inductives       ()
let use_eq_at_higher_order       () = get_use_eq_at_higher_order      ()
let use_hints                    () = get_use_hints                   ()
let use_tactics                  () = get_use_tactics                 ()
let using_facts_from             () = get_using_facts_from            ()
let verify_all                   () = get_verify_all                  ()
let verify_module                () = get_verify_module               ()
let warn_default_effects         () = get_warn_default_effects        ()
let z3_exe                       () = match get_smt () with
                                    | None -> Platform.exe "z3"
                                    | Some s -> s
let z3_cliopt                    () = get_z3cliopt                    ()
let z3_refresh                   () = get_z3refresh                   ()
let z3_rlimit                    () = get_z3rlimit                    ()
let z3_rlimit_factor             () = get_z3rlimit_factor             ()
let z3_seed                      () = get_z3seed                      ()
let z3_timeout                   () = get_z3timeout                   ()
let no_positivity                () = get_no_positivity               ()


let should_extract m =
  not (no_extract m) && (extract_all () ||
  (match get_extract_module () with
  | [] ->
    (match get_extract_namespace () with
     | [] -> true
     | ns -> Util.for_some (Util.starts_with (String.lowercase m)) ns)
  | l -> List.contains (String.lowercase m) l))


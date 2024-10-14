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
open FStar.All
open FStarC.Compiler.Effect
open FStarC.Getopt
open FStarC.BaseTypes
open FStarC.VConfig
open FStarC.Compiler

type codegen_t =
  | OCaml
  | FSharp
  | Krml
  | Plugin
  | PluginNoLib
  | Extension

//let __test_norm_all = Util.mk_ref false

type split_queries_t = | No | OnFailure | Always

type message_format_t = | Json | Human

type option_val =
  | Bool of bool
  | String of string
  | Path of string
  | Int of int
  | List of list option_val
  | Unset

type optionstate = FStarC.Compiler.Util.psmap option_val

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
| EnumStr of list string
  // --codegen OCaml
| OpenEnumStr of list string (* suggested values (not exhaustive) *) & string (* label *)
  // --debug …
| PostProcessed of ((option_val -> option_val) (* validator *) & opt_type (* elem spec *))
  // For options like --extract_module that require post-processing or validation
| Accumulated of opt_type (* elem spec *)
  // For options like --extract_module that can be repeated (LIFO)
| ReverseAccumulated of opt_type (* elem spec *)
  // For options like --include that can be repeated (FIFO)
| WithSideEffect of ((unit -> unit) & opt_type (* elem spec *))
  // For options like --version that have side effects

val defaults                    : list (string & option_val)

val init                        : unit    -> unit  //sets the current options to their defaults
val clear                       : unit    -> unit  //wipes the stack of options, and then inits
val restore_cmd_line_options    : bool -> parse_cmdline_res //inits or clears (if the flag is set) the current options and then sets it to the cmd line

(* Control the option stack *)
(* Briefly, push/pop are used by the interactive mode and internal_*
 * by #push-options/#pop-options. Read the comment in the .fs for more
 * details. *)
val push                        : unit -> unit
val pop                         : unit -> unit
val internal_push               : unit -> unit
val internal_pop                : unit -> bool (* returns whether it worked or not, false should be taken as a hard error *)
val depth                       : unit -> int (* number of elements in internal option stack, besides current. If >0, internal_pop should succeed. *)
val snapshot                    : unit -> (int & unit)
val rollback                    : option int -> unit
val peek                        : unit -> optionstate
val set                         : optionstate -> unit
val set_verification_options    : optionstate -> unit

(* Print the current optionstate as a string that could be passed to fstar.exe, e.g.
"--z3rlimit 25 --include /some/path" *)
val show_options                : unit -> string

val __unit_tests                : unit    -> bool
val __set_unit_tests            : unit    -> unit
val __clear_unit_tests          : unit    -> unit
val parse_cmd_line              : unit    -> parse_cmdline_res & list string
val add_verify_module           : string  -> unit

val set_option_warning_callback : (string -> unit) -> unit
val desc_of_opt_type            : opt_type -> option string
val all_specs_with_types        : list (char & string & opt_type & Pprint.document)
val settable                    : string -> bool

val abort_counter : ref int

val admit_smt_queries           : unit    -> bool
val set_admit_smt_queries       : bool    -> unit
val admit_except                : unit    -> option string
val compat_pre_core_should_register : unit    -> bool
val compat_pre_core_should_check : unit    -> bool
val compat_pre_core_set         : unit    -> bool
val compat_pre_typed_indexed_effects: unit -> bool
val disallow_unification_guards : unit    -> bool
val cache_checked_modules       : unit    -> bool
val cache_off                   : unit    -> bool
val print_cache_version         : unit    -> bool
val cmi                         : unit    -> bool
val codegen                     : unit    -> option codegen_t
val parse_codegen               : string  -> option codegen_t
val codegen_libs                : unit    -> list (list string)
val profile_enabled             : module_name:option string -> profile_phase:string -> bool
val profile_group_by_decl       : unit    -> bool
val defensive                   : unit    -> bool // true if checks should be performed
val defensive_error             : unit    -> bool // true if "error"
val defensive_abort             : unit    -> bool // true if "abort"
val dep                         : unit    -> option string
val detail_errors               : unit    -> bool
val detail_hint_replay          : unit    -> bool
val display_usage               : unit    -> unit
val any_dump_module             : unit    -> bool
val dump_module                 : string  -> bool
val eager_subtyping             : unit    -> bool
val error_contexts              : unit    -> bool
val expose_interfaces           : unit    -> bool
val message_format              : unit    -> message_format_t
val file_list                   : unit    -> list string
val force                       : unit    -> bool
val fstar_bin_directory         : string
val get_option                  : string  -> option_val
val full_context_dependency     : unit    -> bool
val hide_uvar_nums              : unit    -> bool
val hint_info                   : unit    -> bool
val hint_file_for_src           : string  -> string
val ide                         : unit    -> bool
val ide_id_info_off             : unit    -> bool
val set_ide_filename            : string -> unit
val ide_filename                : unit -> option string
val print                       : unit    -> bool
val print_in_place              : unit    -> bool
val initial_fuel                : unit    -> int
val initial_ifuel               : unit    -> int
val interactive                 : unit    -> bool
val keep_query_captions         : unit    -> bool
val lax                         : unit    -> bool
val load                        : unit    -> list string
val load_cmxs                   : unit    -> list string
val legacy_interactive          : unit    -> bool
val lsp_server                  : unit    -> bool
val log_queries                 : unit    -> bool
val log_failing_queries         : unit    -> bool
val log_types                   : unit    -> bool
val max_fuel                    : unit    -> int
val max_ifuel                   : unit    -> int
val ml_ish                      : unit    -> bool
val ml_ish_effect               : unit    -> string
val set_ml_ish                  : unit    -> unit
val no_default_includes         : unit    -> bool
val no_location_info            : unit    -> bool
val no_plugins                  : unit    -> bool
val no_smt                      : unit    -> bool
val normalize_pure_terms_for_extraction
                                : unit    -> bool
val krmloutput                  : unit    -> option string
val list_plugins                : unit    -> bool
val locate                      : unit    -> bool
val locate_lib                  : unit    -> bool
val locate_ocaml                : unit    -> bool
val output_deps_to              : unit    -> option string
val output_dir                  : unit    -> option string
val custom_prims                : unit    -> option string
val cache_dir                   : unit    -> option string
val include_                    : unit    -> list string
val print_bound_var_types       : unit    -> bool
val print_effect_args           : unit    -> bool
val print_expected_failures     : unit    -> bool
val print_implicits             : unit    -> bool
val print_real_names            : unit    -> bool
val print_universes             : unit    -> bool
val print_z3_statistics         : unit    -> bool
val proof_recovery              : unit    -> bool
val quake_lo                    : unit    -> int
val quake_hi                    : unit    -> int
val quake_keep                  : unit    -> bool
val query_cache                 : unit    -> bool
val query_stats                 : unit    -> bool
val read_checked_file           : unit    -> option string
val read_krml_file              : unit    -> option string
val record_hints                : unit    -> bool
val record_options              : unit    -> bool
val retry                       : unit    -> bool
val reuse_hint_for              : unit    -> option string
val report_assumes              : unit    -> option string
val set_option                  : string  -> option_val -> unit
val set_options                 : string -> parse_cmdline_res
val should_be_already_cached    : string  -> bool
val should_print_message        : string  -> bool
val should_extract              : string  -> codegen_t -> bool
val should_check                : string  -> bool (* Should check this module, lax or not. *)
val should_check_file           : string  -> bool (* Should check this file, lax or not. *)
val should_verify               : string  -> bool (* Should check this module with verification enabled. *)
val should_verify_file          : string  -> bool (* Should check this file with verification enabled. *)
val silent                      : unit    -> bool
val smt                         : unit    -> option string
val smtencoding_elim_box        : unit    -> bool
val smtencoding_nl_arith_default: unit    -> bool
val smtencoding_nl_arith_wrapped: unit    -> bool
val smtencoding_nl_arith_native : unit    -> bool
val smtencoding_l_arith_default : unit    -> bool
val smtencoding_l_arith_native  : unit    -> bool
val smtencoding_valid_intro     : unit    -> bool
val smtencoding_valid_elim      : unit    -> bool
val split_queries               : unit    -> split_queries_t
val tactic_raw_binders          : unit    -> bool
val tactics_failhard            : unit    -> bool
val tactics_info                : unit    -> bool
val tactic_trace                : unit    -> bool
val tactic_trace_d              : unit    -> int
val tactics_nbe                 : unit    -> bool
val tcnorm                      : unit    -> bool
val timing                      : unit    -> bool
val trace_error                 : unit    -> bool
val ugly                        : unit    -> bool
val unthrottle_inductives       : unit    -> bool
val unsafe_tactic_exec          : unit    -> bool
val use_eq_at_higher_order      : unit    -> bool
val use_hints                   : unit    -> bool
val use_hint_hashes             : unit    -> bool
val use_native_tactics          : unit    -> option string
val use_tactics                 : unit    -> bool
val using_facts_from            : unit    -> list (list string & bool)
val warn_default_effects        : unit    -> bool
val with_saved_options          : (unit -> 'a) -> 'a
val with_options                : string -> (unit -> 'a) -> 'a
val z3_cliopt                   : unit    -> list string
val z3_smtopt                   : unit    -> list string
val z3_refresh                  : unit    -> bool
val z3_rlimit                   : unit    -> int
val z3_rlimit_factor            : unit    -> int
val z3_seed                     : unit    -> int
val z3_version                  : unit    -> string
val no_positivity               : unit    -> bool
val warn_error                  : unit    -> string
val set_error_flags_callback    : ((unit  -> parse_cmdline_res) -> unit)
val use_nbe                     : unit    -> bool
val use_nbe_for_extraction      : unit    -> bool
val trivial_pre_for_unannotated_effectful_fns
                                : unit    -> bool

(* List of enabled debug toggles. *)
val debug_keys                  : unit    -> list string

(* Whether we are debugging every module and not just the ones
in the cmdline. *)
val debug_all_modules           : unit    -> bool

// HACK ALERT! This is to ensure we have no dependency from Options to Version,
// otherwise, since Version is regenerated all the time, this invalidates the
// whole build tree. A classy technique I learned from the OCaml compiler.
val _version: ref string
val _platform: ref string
val _compiler: ref string
val _date: ref string
val _commit: ref string

val debug_embedding: ref bool
val eager_embedding: ref bool

val get_vconfig : unit -> vconfig
val set_vconfig : vconfig -> unit

instance val showable_codegen_t : Class.Show.showable codegen_t

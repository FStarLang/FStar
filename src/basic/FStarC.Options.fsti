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

open FStarC
open FStarC.Effect
open FStarC.Getopt
open FStarC.BaseTypes
open FStarC.VConfig

(* Set externally, checks if the directory exists and otherwise
logs an issue. Cannot do it here due to circular deps. *)
val check_include_dir : ref (string -> ML unit)

(* Raised when a processing a pragma an a non-settable option
appears there. *)
exception NotSettable of string

type codegen_t =
  | OCaml
  | FSharp
  | Krml
  | Plugin
  | PluginNoLib
  | Extension

//let __test_norm_all = mk_ref false

type split_queries_t = | No | OnFailure | Always

type message_format_t = | Json | Human | Github

type option_val =
  | Bool of bool
  | String of string
  | Path of string
  | Int of int
  | List of list option_val
  | Unset

type optionstate = PSMap.t option_val

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
| PostProcessed of ((option_val -> ML option_val) (* validator *) & opt_type (* elem spec *))
  // For options like --extract_module that require post-processing or validation
| Accumulated of opt_type (* elem spec *)
  // For options like --extract_module that can be repeated (LIFO, accumulate the new element via Cons, at the head)
| ReverseAccumulated of opt_type (* elem spec *)
  // For options like --include that can be repeated (FIFO, accumulate the new element via snoc, at the tail)
| WithSideEffect of ((unit -> ML unit) & opt_type (* elem spec *))

val debug_embedding: ref bool

val eager_embedding: ref bool

val peek                        : unit -> ML optionstate

val internal_push               : unit -> ML unit

val internal_pop                : unit -> ML bool (* returns whether it worked or not, false should be taken as a hard error *)

(* Control the option stack *)
(* Briefly, push/pop are used by the interactive mode and internal_*
 * by #push-options/#pop-options. Read the comment in the .fs for more
 * details. *)
val push                        : unit -> ML unit

val pop                         : unit -> ML unit

val set                         : optionstate -> ML unit

val depth                       : unit -> ML int (* number of elements in internal option stack, besides current. If >0, internal_pop should succeed. *)

val snapshot                    : unit -> ML (int & unit)

val rollback                    : option int -> ML unit

val set_option                  : string  -> option_val -> ML unit

val set_admit_smt_queries       : bool    -> ML unit

  // For options like --version that have side effects

val defaults                    : list (string & option_val)

val init                        : unit    -> ML unit  //sets the current options to their defaults

val clear                       : unit    -> ML unit  //wipes the stack of options, and then inits

val get_option                  : string  -> ML option_val

(* Print the current optionstate as a string that could be passed to fstar.exe, e.g.
"--z3rlimit 25 --include /some/path" *)
val show_options                : unit -> ML string

val set_verification_options    : optionstate -> ML unit

// HACK ALERT! This is to ensure we have no dependency from Options to Version,
// otherwise, since Version is regenerated all the time, this invalidates the
// whole build tree. A classy technique I learned from the OCaml compiler.
val _version: ref string

val _platform: ref string

val _compiler: ref string

val _date: ref string

val _commit: ref string

val add_verify_module           : string  -> ML unit

val desc_of_opt_type            : opt_type -> option string

val abort_counter : ref int

val set_option_warning_callback : (string -> ML unit) -> ML unit

val settable                    : string -> bool

val all_specs_with_types        : list (char & string & opt_type & Pprint.document)

val help_for_option             : string -> ML (option Pprint.document)

val set_error_flags_callback    : ((unit  -> ML parse_cmdline_res) -> ML unit)

val display_usage               : unit    -> ML unit

val fstar_bin_directory         : string

val parse_cmd_line              : unit    -> ML (parse_cmdline_res & list string)

val file_list                   : unit    -> ML (list string)

val restore_cmd_line_options    : bool -> ML parse_cmdline_res //inits or clears (if the flag is set) the current options and then sets it to the cmd line

val with_restored_cmd_line_options : (unit -> ML 'a) -> ML 'a

val should_check                : string  -> ML bool (* Should check this module, lax or not. *)

val should_verify               : string  -> ML bool (* Should check this module with verification enabled. *)

val should_check_file           : string  -> ML bool (* Should check this file, lax or not. *)

val should_verify_file          : string  -> ML bool (* Should check this file with verification enabled. *)

val should_print_message        : string  -> ML bool

val custom_prims                : unit    -> ML (option string)

val admit_smt_queries           : unit    -> ML bool

val admit_except                : unit    -> ML (option string)

val compat_pre_core_should_register : unit    -> ML bool

val compat_pre_core_should_check : unit    -> ML bool

val compat_pre_core_set         : unit    -> ML bool

val compat_pre_typed_indexed_effects: unit -> ML bool

val disallow_unification_guards : unit    -> ML bool

val cache_checked_modules       : unit    -> ML bool

val cache_off                   : unit    -> ML bool

val print_cache_version         : unit    -> ML bool

val cmi                         : unit    -> ML bool

val parse_codegen               : string  -> option codegen_t

val codegen                     : unit    -> ML (option codegen_t)

val codegen_libs                : unit    -> ML (list (list string))

val profile_group_by_decl       : unit    -> ML bool

val defensive                   : unit    -> ML bool // true if checks should be performed

val defensive_error             : unit    -> ML bool // true if "error"

val defensive_abort             : unit    -> ML bool // true if "abort"

val dep                         : unit    -> ML (option string)

val detail_errors               : unit    -> ML bool

val detail_hint_replay          : unit    -> ML bool

val any_dump_module             : unit    -> ML bool

val dump_ast                    : unit    -> ML bool

val dump_module                 : string  -> ML bool

val eager_subtyping             : unit    -> ML bool

val error_contexts              : unit    -> ML bool

val expose_interfaces           : unit    -> ML bool

val interactive                 : unit    -> ML bool

val message_format              : unit    -> ML message_format_t

val force                       : unit    -> ML bool

val help                        : unit    -> ML bool

val hide_uvar_nums              : unit    -> ML bool

val hint_info                   : unit    -> ML bool

val hint_file_for_src           : string  -> ML string

val ide                         : unit    -> ML bool

val ide_id_info_off             : unit    -> ML bool

val set_ide_filename            : string -> ML unit

val ide_filename                : unit -> ML (option string)

val print                       : unit    -> ML bool

val print_in_place              : unit    -> ML bool

val initial_fuel                : unit    -> ML int

val initial_ifuel               : unit    -> ML int

val lang_extensions             : unit    -> ML (list string)

val lax                         : unit    -> ML bool

val load                        : unit    -> ML (list string)

val load_cmxs                   : unit    -> ML (list string)

val log_queries                 : unit    -> ML bool

val log_failing_queries         : unit    -> ML bool

val keep_query_captions         : unit    -> ML bool

val log_types                   : unit    -> ML bool

val max_fuel                    : unit    -> ML int

val max_ifuel                   : unit    -> ML int

val normalize_pure_terms_for_extraction
                                : unit    -> ML bool

val no_location_info            : unit    -> ML bool

val no_prelude                  : unit    -> ML bool

val no_plugins                  : unit    -> ML bool

val no_smt                      : unit    -> ML bool

val output_to                   : unit    -> ML (option string)

val krmloutput                  : unit    -> ML (option string)

val output_deps_to              : unit    -> ML (option string)

val ugly                        : unit    -> ML bool

val print_bound_var_types       : unit    -> ML bool

val print_effect_args           : unit    -> ML bool

val print_expected_failures     : unit    -> ML bool

val print_implicits             : unit    -> ML bool

val print_real_names            : unit    -> ML bool

val print_universes             : unit    -> ML bool

val print_z3_statistics         : unit    -> ML bool

val proof_recovery              : unit    -> ML bool

val quake_lo                    : unit    -> ML int

val quake_hi                    : unit    -> ML int

val quake_keep                  : unit    -> ML bool

val query_cache                 : unit    -> ML bool

val query_stats                 : unit    -> ML bool

val read_checked_file           : unit    -> ML (option string)

val list_plugins                : unit    -> ML bool

val expand_include              : unit    -> ML (option string)

val locate                      : unit    -> ML bool

val locate_lib                  : unit    -> ML bool

val locate_ocaml                : unit    -> ML bool

val locate_file                 : unit    -> ML (option string)

val locate_z3                   : unit    -> ML (option string)

val read_krml_file              : unit    -> ML (option string)

val record_hints                : unit    -> ML bool

val record_options              : unit    -> ML bool

val retry                       : unit    -> ML bool

val reuse_hint_for              : unit    -> ML (option string)

val report_assumes              : unit    -> ML (option string)

val silent                      : unit    -> ML bool

val smt                         : unit    -> ML (option string)

val smtencoding_elim_box        : unit    -> ML bool

val smtencoding_nl_arith_native : unit    -> ML bool

val smtencoding_nl_arith_wrapped: unit    -> ML bool

val smtencoding_nl_arith_default: unit    -> ML bool

val smtencoding_l_arith_native  : unit    -> ML bool

val smtencoding_l_arith_default : unit    -> ML bool

val smtencoding_valid_intro     : unit    -> ML bool

val smtencoding_valid_elim      : unit    -> ML bool

val split_queries               : unit    -> ML split_queries_t

val stats                       : unit    -> ML bool

val tactic_raw_binders          : unit    -> ML bool

val tactics_failhard            : unit    -> ML bool

val tactics_info                : unit    -> ML bool

val tactic_trace                : unit    -> ML bool

val tactic_trace_d              : unit    -> ML int

val tactics_nbe                 : unit    -> ML bool

val tcnorm                      : unit    -> ML bool

val timing                      : unit    -> ML bool

val trace_error                 : unit    -> ML bool

val unthrottle_inductives       : unit    -> ML bool

val unsafe_tactic_exec          : unit    -> ML bool

val use_eq_at_higher_order      : unit    -> ML bool

val use_hints                   : unit    -> ML bool

val use_hint_hashes             : unit    -> ML bool

val use_native_tactics          : unit    -> ML (option string)

val use_tactics                 : unit    -> ML bool

val using_facts_from            : unit    -> ML (list (list string & bool))

val warn_default_effects        : unit    -> ML bool

val warn_error                  : unit    -> ML string

val z3_cliopt                   : unit    -> ML (list string)

val z3_smtopt                   : unit    -> ML (list string)

val z3_refresh                  : unit    -> ML bool

val z3_rlimit                   : unit    -> ML int

val z3_rlimit_factor            : unit    -> ML int

val z3_seed                     : unit    -> ML int

val z3_version                  : unit    -> ML string

val no_positivity               : unit    -> ML bool

val use_nbe                     : unit    -> ML bool

val use_nbe_for_extraction      : unit    -> ML bool

val trivial_pre_for_unannotated_effectful_fns
                                : unit    -> ML bool

(* List of enabled debug toggles. *)
val debug_keys                  : unit    -> ML (list string)

(* Whether we are debugging every module and not just the ones
in the cmdline. *)
val debug_all_modules           : unit    -> ML bool

val with_saved_options          : (unit -> ML 'a) -> ML 'a

val should_extract              : string  -> codegen_t -> ML bool

val should_be_already_cached    : string  -> ML bool

val profile_enabled             : module_name:option string -> profile_phase:string -> ML bool

val set_options                 : string -> ML parse_cmdline_res

val with_options                : string -> (unit -> ML 'a) -> ML 'a

val get_vconfig : unit -> ML vconfig

val set_vconfig : vconfig -> ML unit

instance val showable_codegen_t : Class.Show.showable codegen_t

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
#light "off"

// (c) Microsoft Corporation. All rights reserved
module FStar.Options
open FStar.ST
open FStar.All
open FStar.Getopt
open FStar.BaseTypes

//let __test_norm_all = Util.mk_ref false

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

val defaults                    : list<(string * option_val)>

val init                        : unit    -> unit  //sets the current options to their defaults
val clear                       : unit    -> unit  //wipes the stack of options, and then inits
val restore_cmd_line_options    : bool -> parse_cmdline_res //inits or clears (if the flag is set) the current options and then sets it to the cmd line

type optionstate = Util.smap<option_val>
(* Control the option stack *)
(* Briefly, push/pop are used by the interactive mode and internal_*
 * by #push-options/#pop-options. Read the comment in the .fs for more
 * details. *)
val push                        : unit -> unit
val pop                         : unit -> unit
val internal_push               : unit -> unit
val internal_pop                : unit -> bool (* returns whether it worked or not, false should be taken as a hard error *)
val snapshot                    : unit -> (int * unit)
val rollback                    : option<int> -> unit
val peek                        : unit -> optionstate
val set                         : optionstate -> unit

val __unit_tests                : unit    -> bool
val __set_unit_tests            : unit    -> unit
val __clear_unit_tests          : unit    -> unit
val parse_cmd_line              : unit    -> parse_cmdline_res * list<string>
val add_verify_module           : string  -> unit
val add_light_off_file          : string  -> unit

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

val set_option_warning_callback : (string -> unit) -> unit
val desc_of_opt_type            : opt_type -> option<string>
val all_specs_with_types        : list<(char * string * opt_type * string)>
val settable                    : string -> bool

val abort_counter : ref<int>

val __temp_no_proj              : string  -> bool
val __temp_fast_implicits       : unit    -> bool
val admit_smt_queries           : unit    -> bool
val set_admit_smt_queries       : bool    -> unit
val admit_except                : unit    -> option<string>
val cache_checked_modules       : unit    -> bool
val cache_off                   : unit    -> bool
val print_cache_version         : unit    -> bool
val cmi                         : unit    -> bool
type codegen_t =
    | OCaml | FSharp | Kremlin | Plugin
val codegen                     : unit    -> option<codegen_t>
val codegen_libs                : unit    -> list<list<string>>
val profile_enabled             : module_name:option<string> -> profile_phase:string -> bool
val profile_group_by_decls      : unit    -> bool
val defensive                   : unit    -> bool // true if checks should be performed
val defensive_error             : unit    -> bool // true if "error"
val defensive_abort             : unit    -> bool // true if "abort"
val dep                         : unit    -> option<string>
val detail_errors               : unit    -> bool
val detail_hint_replay          : unit    -> bool
val display_usage               : unit    -> unit
val dont_gen_projectors         : string  -> bool
val dump_module                 : string  -> bool
val eager_subtyping             : unit    -> bool
val expose_interfaces           : unit    -> bool
val file_list                   : unit    -> list<string>
val find_file                   : (string  -> option<string>)
val force                       : unit    -> bool
val fs_typ_app                  : string  -> bool
val fstar_bin_directory         : string
val get_option                  : string  -> option_val
val full_context_dependency     : unit    -> bool
val hide_uvar_nums              : unit    -> bool
val hint_info                   : unit    -> bool
val hint_file_for_src           : string  -> string
val ide                         : unit    -> bool
val include_path                : unit    -> list<string>
val print                       : unit    -> bool
val print_in_place              : unit    -> bool
val initial_fuel                : unit    -> int
val initial_ifuel               : unit    -> int
val interactive                 : unit    -> bool
val keep_query_captions         : unit    -> bool
val lax                         : unit    -> bool
val load                        : unit    -> list<string>
val legacy_interactive          : unit    -> bool
val lsp_server                  : unit    -> bool
val log_queries                 : unit    -> bool
val log_types                   : unit    -> bool
val max_fuel                    : unit    -> int
val max_ifuel                   : unit    -> int
val min_fuel                    : unit    -> int
val ml_ish                      : unit    -> bool
val set_ml_ish                  : unit    -> unit
val no_default_includes         : unit    -> bool
val no_extract                  : string  -> bool
val no_load_fstartaclib         : unit    -> bool
val no_location_info            : unit    -> bool
val no_plugins                  : unit    -> bool
val no_smt                      : unit    -> bool
val normalize_pure_terms_for_extraction
                                : unit    -> bool
val output_dir                  : unit    -> option<string>
val prepend_cache_dir           : string  -> string
val prepend_output_dir          : string  -> string
val prims                       : unit    -> string
val prims_basename              : unit    -> string
val pervasives                  : unit    -> string
val pervasives_basename         : unit    -> string
val pervasives_native_basename  : unit    -> string
val print_bound_var_types       : unit    -> bool
val print_effect_args           : unit    -> bool
val print_expected_failures     : unit    -> bool
val print_implicits             : unit    -> bool
val print_real_names            : unit    -> bool
val print_universes             : unit    -> bool
val print_z3_statistics         : unit    -> bool
val quake_lo                    : unit    -> int
val quake_hi                    : unit    -> int
val quake_keep                  : unit    -> bool
val query_stats                 : unit    -> bool
val record_hints                : unit    -> bool
val record_options              : unit    -> bool
val retry                       : unit    -> bool
val reuse_hint_for              : unit    -> option<string>
val report_assumes              : unit    -> option<string>
val set_option                  : string  -> option_val -> unit
val set_options                 : string -> parse_cmdline_res
val should_be_already_cached    : string  -> bool
val should_print_message        : string  -> bool
val should_extract              : string  -> bool
val should_check                : string  -> bool (* Should check this module, lax or not. *)
val should_check_file           : string  -> bool (* Should check this file, lax or not. *)
val should_verify               : string  -> bool (* Should check this module with verification enabled. *)
val should_verify_file          : string  -> bool (* Should check this file with verification enabled. *)
val silent                      : unit    -> bool
val smtencoding_elim_box        : unit    -> bool
val smtencoding_nl_arith_default: unit    -> bool
val smtencoding_nl_arith_wrapped: unit    -> bool
val smtencoding_nl_arith_native : unit    -> bool
val smtencoding_l_arith_default : unit    -> bool
val smtencoding_l_arith_native  : unit    -> bool
val smtencoding_valid_intro     : unit    -> bool
val smtencoding_valid_elim      : unit    -> bool
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
val use_native_tactics          : unit    -> option<string>
val use_tactics                 : unit    -> bool
val using_facts_from            : unit    -> list<(list<string> * bool)>
val vcgen_optimize_bind_as_seq  : unit    -> bool
val vcgen_decorate_with_type    : unit    -> bool
val warn_default_effects        : unit    -> bool
val with_saved_options          : (unit -> 'a) -> 'a
val z3_exe                      : unit    -> string
val z3_cliopt                   : unit    -> list<string>
val z3_refresh                  : unit    -> bool
val z3_rlimit                   : unit    -> int
val z3_rlimit_factor            : unit    -> int
val z3_seed                     : unit    -> int
val use_two_phase_tc            : unit    -> bool
val no_positivity               : unit    -> bool
val ml_no_eta_expand_coertions  : unit    -> bool
val warn_error                  : unit    -> string
val set_error_flags_callback    : ((unit  -> parse_cmdline_res) -> unit)
val use_nbe                     : unit    -> bool
val use_nbe_for_extraction      : unit    -> bool
val trivial_pre_for_unannotated_effectful_fns
                                : unit    -> bool

(* True iff the user passed '--debug M' for some M *)
val debug_any                   : unit    -> bool

(* True for M when the user passed '--debug M' *)
val debug_module                : string  -> bool

(* True for M and L when the user passed '--debug M --debug_level L'
 * (and possibly more) *)
val debug_at_level              : string  -> debug_level_t -> bool

(* True for L when the user passed '--debug_level L'
 * (and possibly more, but independent of --debug) *)
val debug_at_level_no_module    : debug_level_t -> bool

// HACK ALERT! This is to ensure we have no dependency from Options to Version,
// otherwise, since Version is regenerated all the time, this invalidates the
// whole build tree. A classy technique I learned from the OCaml compiler.
val _version: ref<string>
val _platform: ref<string>
val _compiler: ref<string>
val _date: ref<string>
val _commit: ref<string>

val debug_embedding: ref<bool>
val eager_embedding: ref<bool>

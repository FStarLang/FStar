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
open FStar.Getopt

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

type options =
    | Set
    | Reset
    | Restore

val defaults                    : list<(string * option_val)>
val docs                        : unit -> list<(string * string)>

val init                        : unit    -> unit  //sets the current options to their defaults
val clear                       : unit    -> unit  //wipes the stack of options, and then inits
val restore_cmd_line_options    : bool    -> parse_cmdline_res //inits or clears (if the flag is set) the current options and then sets it to the cmd line

val __unit_tests                : unit    -> bool
val __set_unit_tests            : unit    -> unit
val __clear_unit_tests          : unit    -> unit
val parse_cmd_line              : unit    -> parse_cmdline_res * list<string>
val add_verify_module           : string  -> unit

val add_light_off_file          : string  -> unit

val __temp_no_proj              : string  -> bool
val admit_smt_queries           : unit    -> bool
val codegen                     : unit    -> option<string>
val codegen_libs                : unit    -> list<list<string>>
val debug_any                   : unit    -> bool
val debug_at_level              : string  -> debug_level_t -> bool
val dep                         : unit    -> option<string>
val detail_errors               : unit    -> bool
val display_usage               : unit    -> unit
val doc                         : unit    -> bool
val dont_gen_projectors         : string  -> bool
val dump_module                 : string  -> bool
val eager_inference             : unit    -> bool
val explicit_deps               : unit    -> bool
val extract_all                 : unit    -> bool
val file_list                   : unit    -> list<string>
val find_file                   : string  -> option<string>
val fs_typ_app                  : string  -> bool
val fstar_home                  : unit    -> string
val get_option                  : string  -> option_val
val full_context_dependency     : unit    -> bool
val hide_genident_nums          : unit    -> bool
val hide_uvar_nums              : unit    -> bool
val hint_info                   : unit    -> bool
val ide                         : unit    -> bool
val include_path                : unit    -> list<string>
val indent                      : unit    -> bool
val initial_fuel                : unit    -> int
val initial_ifuel               : unit    -> int
val interactive                 : unit    -> bool
val lax                         : unit    -> bool
val legacy_interactive          : unit    -> bool
val log_queries                 : unit    -> bool
val log_types                   : unit    -> bool
val max_fuel                    : unit    -> int
val max_ifuel                   : unit    -> int
val min_fuel                    : unit    -> int
val ml_ish                      : unit    -> bool
val set_ml_ish                  : unit    -> unit
val n_cores                     : unit    -> int
val no_default_includes         : unit    -> bool
val no_extract                  : string  -> bool
val no_location_info            : unit    -> bool
val norm_then_print             : unit    -> bool
val output_dir                  : unit    -> option<string>
val pop                         : unit    -> unit
val prepend_output_dir          : string  -> string
val prims                       : unit    -> string
val prims_basename              : unit    -> string
val pervasives                  : unit    -> string
val pervasives_basename         : unit    -> string
val print_bound_var_types       : unit    -> bool
val print_effect_args           : unit    -> bool
val print_fuels                 : unit    -> bool
val print_implicits             : unit    -> bool
val print_real_names            : unit    -> bool
val print_universes             : unit    -> bool
val print_z3_statistics         : unit    -> bool
val push                        : unit    -> unit
val record_hints                : unit    -> bool
val check_hints                 : unit    -> bool
val reuse_hint_for              : unit    -> option<string>
val set_option                  : string  -> option_val -> unit
val set_options                 : options -> string -> parse_cmdline_res
val should_print_message        : string  -> bool
val should_extract              : string  -> bool
val should_verify               : string  -> bool
val silent                      : unit    -> bool
val smtencoding_elim_box        : unit -> bool
val smtencoding_nl_arith_default: unit -> bool
val smtencoding_nl_arith_wrapped: unit -> bool
val smtencoding_nl_arith_native : unit -> bool
val smtencoding_l_arith_default : unit -> bool
val smtencoding_l_arith_native  : unit -> bool
val split_cases                 : unit    -> int
val timing                      : unit    -> bool
val trace_error                 : unit    -> bool
val ugly                        : unit    -> bool
val unthrottle_inductives       : unit    -> bool
val use_eq_at_higher_order      : unit    -> bool
val use_hints                   : unit    -> bool
val use_tactics                 : unit    -> bool
val using_facts_from            : unit    -> option<list<string>>
val verify_all                  : unit    -> bool
val verify_module               : unit    -> list<string>
val warn_default_effects        : unit    -> bool
val with_saved_options          : (unit -> 'a) -> 'a
val z3_exe                      : unit    -> string
val z3_cliopt                   : unit    -> list<string>
val z3_refresh                  : unit    -> bool
val z3_rlimit                   : unit    -> int
val z3_rlimit_factor            : unit    -> int
val z3_seed                     : unit    -> int
val z3_timeout                  : unit    -> int
val no_positivity               : unit    -> bool

// HACK ALERT! This is to ensure we have no dependency from Options to Version,
// otherwise, since Version is regenerated all the time, this invalidates the
// whole build tree. A classy technique I learned from the OCaml compiler.
val _version: ref<string>
val _platform: ref<string>
val _compiler: ref<string>
val _date: ref<string>
val _commit: ref<string>

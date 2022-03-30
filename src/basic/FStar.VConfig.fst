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
module FStar.VConfig

open FStar.Compiler.Effect module List = FStar.Compiler.List

(* A type storing all options relevant to verification, used as
the "format" for sigelt_opts and check_with (in reflection). *)

type vconfig = {
  initial_fuel                              : int;
  max_fuel                                  : int;
  initial_ifuel                             : int;
  max_ifuel                                 : int;
  detail_errors                             : bool;
  detail_hint_replay                        : bool;
  no_smt                                    : bool;
  quake_lo                                  : int;
  quake_hi                                  : int;
  quake_keep                                : bool;
  retry                                     : bool;
  smtencoding_elim_box                      : bool;
  smtencoding_nl_arith_repr                 : string;
  smtencoding_l_arith_repr                  : string;
  smtencoding_valid_intro                   : bool;
  smtencoding_valid_elim                    : bool;
  tcnorm                                    : bool;
  no_plugins                                : bool;
  no_tactics                                : bool;
  vcgen_optimize_bind_as_seq                : option<string>;
  z3cliopt                                  : list<string>;
  z3refresh                                 : bool;
  z3rlimit                                  : int;
  z3rlimit_factor                           : int;
  z3seed                                    : int;
  trivial_pre_for_unannotated_effectful_fns : bool;
  reuse_hint_for                            : option<string>;
}

(*
   Copyright 2008-2018 Microsoft Research

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
module FStar.Stubs.VConfig

(** This type represents the set of verification-relevant options used
    to check a particular definition. It can be read from tactics via
    sigelt_opts and set via the check_with attribute.

    This type, and the whole module, mirror FStar.VConfig in F* sources.
 *)
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
  z3cliopt                                  : list string;
  z3smtopt                                  : list string;  
  z3refresh                                 : bool;
  z3rlimit                                  : int;
  z3rlimit_factor                           : int;
  z3seed                                    : int;
  z3version                                 : string;
  trivial_pre_for_unannotated_effectful_fns : bool;
  reuse_hint_for                            : option string;
}

(** Marker to check a sigelt with a particular vconfig *)
irreducible
let check_with (vcfg : vconfig) : unit = ()

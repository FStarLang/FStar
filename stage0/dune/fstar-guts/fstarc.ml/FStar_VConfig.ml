open Prims
type vconfig =
  {
  initial_fuel: Prims.int ;
  max_fuel: Prims.int ;
  initial_ifuel: Prims.int ;
  max_ifuel: Prims.int ;
  no_smt: Prims.bool ;
  quake_lo: Prims.int ;
  quake_hi: Prims.int ;
  quake_keep: Prims.bool ;
  retry: Prims.bool ;
  smtencoding_elim_box: Prims.bool ;
  smtencoding_nl_arith_repr: Prims.string ;
  smtencoding_l_arith_repr: Prims.string ;
  tcnorm: Prims.bool ;
  no_plugins: Prims.bool ;
  no_tactics: Prims.bool ;
  z3cliopt: Prims.string Prims.list ;
  z3smtopt: Prims.string Prims.list ;
  z3refresh: Prims.bool ;
  z3rlimit: Prims.int ;
  z3rlimit_factor: Prims.int ;
  z3seed: Prims.int ;
  z3version: Prims.string ;
  trivial_pre_for_unannotated_effectful_fns: Prims.bool }
let __proj__Mkvconfig__item__initial_fuel (projectee : vconfig) : Prims.int=
  match projectee with
  | { initial_fuel; max_fuel; initial_ifuel; max_ifuel; no_smt; quake_lo;
      quake_hi; quake_keep; retry; smtencoding_elim_box;
      smtencoding_nl_arith_repr; smtencoding_l_arith_repr; tcnorm;
      no_plugins; no_tactics; z3cliopt; z3smtopt; z3refresh; z3rlimit;
      z3rlimit_factor; z3seed; z3version;
      trivial_pre_for_unannotated_effectful_fns;_} -> initial_fuel
let __proj__Mkvconfig__item__max_fuel (projectee : vconfig) : Prims.int=
  match projectee with
  | { initial_fuel; max_fuel; initial_ifuel; max_ifuel; no_smt; quake_lo;
      quake_hi; quake_keep; retry; smtencoding_elim_box;
      smtencoding_nl_arith_repr; smtencoding_l_arith_repr; tcnorm;
      no_plugins; no_tactics; z3cliopt; z3smtopt; z3refresh; z3rlimit;
      z3rlimit_factor; z3seed; z3version;
      trivial_pre_for_unannotated_effectful_fns;_} -> max_fuel
let __proj__Mkvconfig__item__initial_ifuel (projectee : vconfig) : Prims.int=
  match projectee with
  | { initial_fuel; max_fuel; initial_ifuel; max_ifuel; no_smt; quake_lo;
      quake_hi; quake_keep; retry; smtencoding_elim_box;
      smtencoding_nl_arith_repr; smtencoding_l_arith_repr; tcnorm;
      no_plugins; no_tactics; z3cliopt; z3smtopt; z3refresh; z3rlimit;
      z3rlimit_factor; z3seed; z3version;
      trivial_pre_for_unannotated_effectful_fns;_} -> initial_ifuel
let __proj__Mkvconfig__item__max_ifuel (projectee : vconfig) : Prims.int=
  match projectee with
  | { initial_fuel; max_fuel; initial_ifuel; max_ifuel; no_smt; quake_lo;
      quake_hi; quake_keep; retry; smtencoding_elim_box;
      smtencoding_nl_arith_repr; smtencoding_l_arith_repr; tcnorm;
      no_plugins; no_tactics; z3cliopt; z3smtopt; z3refresh; z3rlimit;
      z3rlimit_factor; z3seed; z3version;
      trivial_pre_for_unannotated_effectful_fns;_} -> max_ifuel
let __proj__Mkvconfig__item__no_smt (projectee : vconfig) : Prims.bool=
  match projectee with
  | { initial_fuel; max_fuel; initial_ifuel; max_ifuel; no_smt; quake_lo;
      quake_hi; quake_keep; retry; smtencoding_elim_box;
      smtencoding_nl_arith_repr; smtencoding_l_arith_repr; tcnorm;
      no_plugins; no_tactics; z3cliopt; z3smtopt; z3refresh; z3rlimit;
      z3rlimit_factor; z3seed; z3version;
      trivial_pre_for_unannotated_effectful_fns;_} -> no_smt
let __proj__Mkvconfig__item__quake_lo (projectee : vconfig) : Prims.int=
  match projectee with
  | { initial_fuel; max_fuel; initial_ifuel; max_ifuel; no_smt; quake_lo;
      quake_hi; quake_keep; retry; smtencoding_elim_box;
      smtencoding_nl_arith_repr; smtencoding_l_arith_repr; tcnorm;
      no_plugins; no_tactics; z3cliopt; z3smtopt; z3refresh; z3rlimit;
      z3rlimit_factor; z3seed; z3version;
      trivial_pre_for_unannotated_effectful_fns;_} -> quake_lo
let __proj__Mkvconfig__item__quake_hi (projectee : vconfig) : Prims.int=
  match projectee with
  | { initial_fuel; max_fuel; initial_ifuel; max_ifuel; no_smt; quake_lo;
      quake_hi; quake_keep; retry; smtencoding_elim_box;
      smtencoding_nl_arith_repr; smtencoding_l_arith_repr; tcnorm;
      no_plugins; no_tactics; z3cliopt; z3smtopt; z3refresh; z3rlimit;
      z3rlimit_factor; z3seed; z3version;
      trivial_pre_for_unannotated_effectful_fns;_} -> quake_hi
let __proj__Mkvconfig__item__quake_keep (projectee : vconfig) : Prims.bool=
  match projectee with
  | { initial_fuel; max_fuel; initial_ifuel; max_ifuel; no_smt; quake_lo;
      quake_hi; quake_keep; retry; smtencoding_elim_box;
      smtencoding_nl_arith_repr; smtencoding_l_arith_repr; tcnorm;
      no_plugins; no_tactics; z3cliopt; z3smtopt; z3refresh; z3rlimit;
      z3rlimit_factor; z3seed; z3version;
      trivial_pre_for_unannotated_effectful_fns;_} -> quake_keep
let __proj__Mkvconfig__item__retry (projectee : vconfig) : Prims.bool=
  match projectee with
  | { initial_fuel; max_fuel; initial_ifuel; max_ifuel; no_smt; quake_lo;
      quake_hi; quake_keep; retry; smtencoding_elim_box;
      smtencoding_nl_arith_repr; smtencoding_l_arith_repr; tcnorm;
      no_plugins; no_tactics; z3cliopt; z3smtopt; z3refresh; z3rlimit;
      z3rlimit_factor; z3seed; z3version;
      trivial_pre_for_unannotated_effectful_fns;_} -> retry
let __proj__Mkvconfig__item__smtencoding_elim_box (projectee : vconfig) :
  Prims.bool=
  match projectee with
  | { initial_fuel; max_fuel; initial_ifuel; max_ifuel; no_smt; quake_lo;
      quake_hi; quake_keep; retry; smtencoding_elim_box;
      smtencoding_nl_arith_repr; smtencoding_l_arith_repr; tcnorm;
      no_plugins; no_tactics; z3cliopt; z3smtopt; z3refresh; z3rlimit;
      z3rlimit_factor; z3seed; z3version;
      trivial_pre_for_unannotated_effectful_fns;_} -> smtencoding_elim_box
let __proj__Mkvconfig__item__smtencoding_nl_arith_repr (projectee : vconfig)
  : Prims.string=
  match projectee with
  | { initial_fuel; max_fuel; initial_ifuel; max_ifuel; no_smt; quake_lo;
      quake_hi; quake_keep; retry; smtencoding_elim_box;
      smtencoding_nl_arith_repr; smtencoding_l_arith_repr; tcnorm;
      no_plugins; no_tactics; z3cliopt; z3smtopt; z3refresh; z3rlimit;
      z3rlimit_factor; z3seed; z3version;
      trivial_pre_for_unannotated_effectful_fns;_} ->
      smtencoding_nl_arith_repr
let __proj__Mkvconfig__item__smtencoding_l_arith_repr (projectee : vconfig) :
  Prims.string=
  match projectee with
  | { initial_fuel; max_fuel; initial_ifuel; max_ifuel; no_smt; quake_lo;
      quake_hi; quake_keep; retry; smtencoding_elim_box;
      smtencoding_nl_arith_repr; smtencoding_l_arith_repr; tcnorm;
      no_plugins; no_tactics; z3cliopt; z3smtopt; z3refresh; z3rlimit;
      z3rlimit_factor; z3seed; z3version;
      trivial_pre_for_unannotated_effectful_fns;_} ->
      smtencoding_l_arith_repr
let __proj__Mkvconfig__item__tcnorm (projectee : vconfig) : Prims.bool=
  match projectee with
  | { initial_fuel; max_fuel; initial_ifuel; max_ifuel; no_smt; quake_lo;
      quake_hi; quake_keep; retry; smtencoding_elim_box;
      smtencoding_nl_arith_repr; smtencoding_l_arith_repr; tcnorm;
      no_plugins; no_tactics; z3cliopt; z3smtopt; z3refresh; z3rlimit;
      z3rlimit_factor; z3seed; z3version;
      trivial_pre_for_unannotated_effectful_fns;_} -> tcnorm
let __proj__Mkvconfig__item__no_plugins (projectee : vconfig) : Prims.bool=
  match projectee with
  | { initial_fuel; max_fuel; initial_ifuel; max_ifuel; no_smt; quake_lo;
      quake_hi; quake_keep; retry; smtencoding_elim_box;
      smtencoding_nl_arith_repr; smtencoding_l_arith_repr; tcnorm;
      no_plugins; no_tactics; z3cliopt; z3smtopt; z3refresh; z3rlimit;
      z3rlimit_factor; z3seed; z3version;
      trivial_pre_for_unannotated_effectful_fns;_} -> no_plugins
let __proj__Mkvconfig__item__no_tactics (projectee : vconfig) : Prims.bool=
  match projectee with
  | { initial_fuel; max_fuel; initial_ifuel; max_ifuel; no_smt; quake_lo;
      quake_hi; quake_keep; retry; smtencoding_elim_box;
      smtencoding_nl_arith_repr; smtencoding_l_arith_repr; tcnorm;
      no_plugins; no_tactics; z3cliopt; z3smtopt; z3refresh; z3rlimit;
      z3rlimit_factor; z3seed; z3version;
      trivial_pre_for_unannotated_effectful_fns;_} -> no_tactics
let __proj__Mkvconfig__item__z3cliopt (projectee : vconfig) :
  Prims.string Prims.list=
  match projectee with
  | { initial_fuel; max_fuel; initial_ifuel; max_ifuel; no_smt; quake_lo;
      quake_hi; quake_keep; retry; smtencoding_elim_box;
      smtencoding_nl_arith_repr; smtencoding_l_arith_repr; tcnorm;
      no_plugins; no_tactics; z3cliopt; z3smtopt; z3refresh; z3rlimit;
      z3rlimit_factor; z3seed; z3version;
      trivial_pre_for_unannotated_effectful_fns;_} -> z3cliopt
let __proj__Mkvconfig__item__z3smtopt (projectee : vconfig) :
  Prims.string Prims.list=
  match projectee with
  | { initial_fuel; max_fuel; initial_ifuel; max_ifuel; no_smt; quake_lo;
      quake_hi; quake_keep; retry; smtencoding_elim_box;
      smtencoding_nl_arith_repr; smtencoding_l_arith_repr; tcnorm;
      no_plugins; no_tactics; z3cliopt; z3smtopt; z3refresh; z3rlimit;
      z3rlimit_factor; z3seed; z3version;
      trivial_pre_for_unannotated_effectful_fns;_} -> z3smtopt
let __proj__Mkvconfig__item__z3refresh (projectee : vconfig) : Prims.bool=
  match projectee with
  | { initial_fuel; max_fuel; initial_ifuel; max_ifuel; no_smt; quake_lo;
      quake_hi; quake_keep; retry; smtencoding_elim_box;
      smtencoding_nl_arith_repr; smtencoding_l_arith_repr; tcnorm;
      no_plugins; no_tactics; z3cliopt; z3smtopt; z3refresh; z3rlimit;
      z3rlimit_factor; z3seed; z3version;
      trivial_pre_for_unannotated_effectful_fns;_} -> z3refresh
let __proj__Mkvconfig__item__z3rlimit (projectee : vconfig) : Prims.int=
  match projectee with
  | { initial_fuel; max_fuel; initial_ifuel; max_ifuel; no_smt; quake_lo;
      quake_hi; quake_keep; retry; smtencoding_elim_box;
      smtencoding_nl_arith_repr; smtencoding_l_arith_repr; tcnorm;
      no_plugins; no_tactics; z3cliopt; z3smtopt; z3refresh; z3rlimit;
      z3rlimit_factor; z3seed; z3version;
      trivial_pre_for_unannotated_effectful_fns;_} -> z3rlimit
let __proj__Mkvconfig__item__z3rlimit_factor (projectee : vconfig) :
  Prims.int=
  match projectee with
  | { initial_fuel; max_fuel; initial_ifuel; max_ifuel; no_smt; quake_lo;
      quake_hi; quake_keep; retry; smtencoding_elim_box;
      smtencoding_nl_arith_repr; smtencoding_l_arith_repr; tcnorm;
      no_plugins; no_tactics; z3cliopt; z3smtopt; z3refresh; z3rlimit;
      z3rlimit_factor; z3seed; z3version;
      trivial_pre_for_unannotated_effectful_fns;_} -> z3rlimit_factor
let __proj__Mkvconfig__item__z3seed (projectee : vconfig) : Prims.int=
  match projectee with
  | { initial_fuel; max_fuel; initial_ifuel; max_ifuel; no_smt; quake_lo;
      quake_hi; quake_keep; retry; smtencoding_elim_box;
      smtencoding_nl_arith_repr; smtencoding_l_arith_repr; tcnorm;
      no_plugins; no_tactics; z3cliopt; z3smtopt; z3refresh; z3rlimit;
      z3rlimit_factor; z3seed; z3version;
      trivial_pre_for_unannotated_effectful_fns;_} -> z3seed
let __proj__Mkvconfig__item__z3version (projectee : vconfig) : Prims.string=
  match projectee with
  | { initial_fuel; max_fuel; initial_ifuel; max_ifuel; no_smt; quake_lo;
      quake_hi; quake_keep; retry; smtencoding_elim_box;
      smtencoding_nl_arith_repr; smtencoding_l_arith_repr; tcnorm;
      no_plugins; no_tactics; z3cliopt; z3smtopt; z3refresh; z3rlimit;
      z3rlimit_factor; z3seed; z3version;
      trivial_pre_for_unannotated_effectful_fns;_} -> z3version
let __proj__Mkvconfig__item__trivial_pre_for_unannotated_effectful_fns
  (projectee : vconfig) : Prims.bool=
  match projectee with
  | { initial_fuel; max_fuel; initial_ifuel; max_ifuel; no_smt; quake_lo;
      quake_hi; quake_keep; retry; smtencoding_elim_box;
      smtencoding_nl_arith_repr; smtencoding_l_arith_repr; tcnorm;
      no_plugins; no_tactics; z3cliopt; z3smtopt; z3refresh; z3rlimit;
      z3rlimit_factor; z3seed; z3version;
      trivial_pre_for_unannotated_effectful_fns;_} ->
      trivial_pre_for_unannotated_effectful_fns

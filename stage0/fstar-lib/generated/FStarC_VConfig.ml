open Prims
type vconfig =
  {
  initial_fuel: Prims.int ;
  max_fuel: Prims.int ;
  initial_ifuel: Prims.int ;
  max_ifuel: Prims.int ;
  detail_errors: Prims.bool ;
  detail_hint_replay: Prims.bool ;
  no_smt: Prims.bool ;
  quake_lo: Prims.int ;
  quake_hi: Prims.int ;
  quake_keep: Prims.bool ;
  retry: Prims.bool ;
  smtencoding_elim_box: Prims.bool ;
  smtencoding_nl_arith_repr: Prims.string ;
  smtencoding_l_arith_repr: Prims.string ;
  smtencoding_valid_intro: Prims.bool ;
  smtencoding_valid_elim: Prims.bool ;
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
  trivial_pre_for_unannotated_effectful_fns: Prims.bool ;
  reuse_hint_for: Prims.string FStar_Pervasives_Native.option }
let (__proj__Mkvconfig__item__initial_fuel : vconfig -> Prims.int) =
  fun projectee ->
    match projectee with
    | { initial_fuel; max_fuel; initial_ifuel; max_ifuel; detail_errors;
        detail_hint_replay; no_smt; quake_lo; quake_hi; quake_keep; retry;
        smtencoding_elim_box; smtencoding_nl_arith_repr;
        smtencoding_l_arith_repr; smtencoding_valid_intro;
        smtencoding_valid_elim; tcnorm; no_plugins; no_tactics; z3cliopt;
        z3smtopt; z3refresh; z3rlimit; z3rlimit_factor; z3seed; z3version;
        trivial_pre_for_unannotated_effectful_fns; reuse_hint_for;_} ->
        initial_fuel
let (__proj__Mkvconfig__item__max_fuel : vconfig -> Prims.int) =
  fun projectee ->
    match projectee with
    | { initial_fuel; max_fuel; initial_ifuel; max_ifuel; detail_errors;
        detail_hint_replay; no_smt; quake_lo; quake_hi; quake_keep; retry;
        smtencoding_elim_box; smtencoding_nl_arith_repr;
        smtencoding_l_arith_repr; smtencoding_valid_intro;
        smtencoding_valid_elim; tcnorm; no_plugins; no_tactics; z3cliopt;
        z3smtopt; z3refresh; z3rlimit; z3rlimit_factor; z3seed; z3version;
        trivial_pre_for_unannotated_effectful_fns; reuse_hint_for;_} ->
        max_fuel
let (__proj__Mkvconfig__item__initial_ifuel : vconfig -> Prims.int) =
  fun projectee ->
    match projectee with
    | { initial_fuel; max_fuel; initial_ifuel; max_ifuel; detail_errors;
        detail_hint_replay; no_smt; quake_lo; quake_hi; quake_keep; retry;
        smtencoding_elim_box; smtencoding_nl_arith_repr;
        smtencoding_l_arith_repr; smtencoding_valid_intro;
        smtencoding_valid_elim; tcnorm; no_plugins; no_tactics; z3cliopt;
        z3smtopt; z3refresh; z3rlimit; z3rlimit_factor; z3seed; z3version;
        trivial_pre_for_unannotated_effectful_fns; reuse_hint_for;_} ->
        initial_ifuel
let (__proj__Mkvconfig__item__max_ifuel : vconfig -> Prims.int) =
  fun projectee ->
    match projectee with
    | { initial_fuel; max_fuel; initial_ifuel; max_ifuel; detail_errors;
        detail_hint_replay; no_smt; quake_lo; quake_hi; quake_keep; retry;
        smtencoding_elim_box; smtencoding_nl_arith_repr;
        smtencoding_l_arith_repr; smtencoding_valid_intro;
        smtencoding_valid_elim; tcnorm; no_plugins; no_tactics; z3cliopt;
        z3smtopt; z3refresh; z3rlimit; z3rlimit_factor; z3seed; z3version;
        trivial_pre_for_unannotated_effectful_fns; reuse_hint_for;_} ->
        max_ifuel
let (__proj__Mkvconfig__item__detail_errors : vconfig -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { initial_fuel; max_fuel; initial_ifuel; max_ifuel; detail_errors;
        detail_hint_replay; no_smt; quake_lo; quake_hi; quake_keep; retry;
        smtencoding_elim_box; smtencoding_nl_arith_repr;
        smtencoding_l_arith_repr; smtencoding_valid_intro;
        smtencoding_valid_elim; tcnorm; no_plugins; no_tactics; z3cliopt;
        z3smtopt; z3refresh; z3rlimit; z3rlimit_factor; z3seed; z3version;
        trivial_pre_for_unannotated_effectful_fns; reuse_hint_for;_} ->
        detail_errors
let (__proj__Mkvconfig__item__detail_hint_replay : vconfig -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { initial_fuel; max_fuel; initial_ifuel; max_ifuel; detail_errors;
        detail_hint_replay; no_smt; quake_lo; quake_hi; quake_keep; retry;
        smtencoding_elim_box; smtencoding_nl_arith_repr;
        smtencoding_l_arith_repr; smtencoding_valid_intro;
        smtencoding_valid_elim; tcnorm; no_plugins; no_tactics; z3cliopt;
        z3smtopt; z3refresh; z3rlimit; z3rlimit_factor; z3seed; z3version;
        trivial_pre_for_unannotated_effectful_fns; reuse_hint_for;_} ->
        detail_hint_replay
let (__proj__Mkvconfig__item__no_smt : vconfig -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { initial_fuel; max_fuel; initial_ifuel; max_ifuel; detail_errors;
        detail_hint_replay; no_smt; quake_lo; quake_hi; quake_keep; retry;
        smtencoding_elim_box; smtencoding_nl_arith_repr;
        smtencoding_l_arith_repr; smtencoding_valid_intro;
        smtencoding_valid_elim; tcnorm; no_plugins; no_tactics; z3cliopt;
        z3smtopt; z3refresh; z3rlimit; z3rlimit_factor; z3seed; z3version;
        trivial_pre_for_unannotated_effectful_fns; reuse_hint_for;_} ->
        no_smt
let (__proj__Mkvconfig__item__quake_lo : vconfig -> Prims.int) =
  fun projectee ->
    match projectee with
    | { initial_fuel; max_fuel; initial_ifuel; max_ifuel; detail_errors;
        detail_hint_replay; no_smt; quake_lo; quake_hi; quake_keep; retry;
        smtencoding_elim_box; smtencoding_nl_arith_repr;
        smtencoding_l_arith_repr; smtencoding_valid_intro;
        smtencoding_valid_elim; tcnorm; no_plugins; no_tactics; z3cliopt;
        z3smtopt; z3refresh; z3rlimit; z3rlimit_factor; z3seed; z3version;
        trivial_pre_for_unannotated_effectful_fns; reuse_hint_for;_} ->
        quake_lo
let (__proj__Mkvconfig__item__quake_hi : vconfig -> Prims.int) =
  fun projectee ->
    match projectee with
    | { initial_fuel; max_fuel; initial_ifuel; max_ifuel; detail_errors;
        detail_hint_replay; no_smt; quake_lo; quake_hi; quake_keep; retry;
        smtencoding_elim_box; smtencoding_nl_arith_repr;
        smtencoding_l_arith_repr; smtencoding_valid_intro;
        smtencoding_valid_elim; tcnorm; no_plugins; no_tactics; z3cliopt;
        z3smtopt; z3refresh; z3rlimit; z3rlimit_factor; z3seed; z3version;
        trivial_pre_for_unannotated_effectful_fns; reuse_hint_for;_} ->
        quake_hi
let (__proj__Mkvconfig__item__quake_keep : vconfig -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { initial_fuel; max_fuel; initial_ifuel; max_ifuel; detail_errors;
        detail_hint_replay; no_smt; quake_lo; quake_hi; quake_keep; retry;
        smtencoding_elim_box; smtencoding_nl_arith_repr;
        smtencoding_l_arith_repr; smtencoding_valid_intro;
        smtencoding_valid_elim; tcnorm; no_plugins; no_tactics; z3cliopt;
        z3smtopt; z3refresh; z3rlimit; z3rlimit_factor; z3seed; z3version;
        trivial_pre_for_unannotated_effectful_fns; reuse_hint_for;_} ->
        quake_keep
let (__proj__Mkvconfig__item__retry : vconfig -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { initial_fuel; max_fuel; initial_ifuel; max_ifuel; detail_errors;
        detail_hint_replay; no_smt; quake_lo; quake_hi; quake_keep; retry;
        smtencoding_elim_box; smtencoding_nl_arith_repr;
        smtencoding_l_arith_repr; smtencoding_valid_intro;
        smtencoding_valid_elim; tcnorm; no_plugins; no_tactics; z3cliopt;
        z3smtopt; z3refresh; z3rlimit; z3rlimit_factor; z3seed; z3version;
        trivial_pre_for_unannotated_effectful_fns; reuse_hint_for;_} -> retry
let (__proj__Mkvconfig__item__smtencoding_elim_box : vconfig -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { initial_fuel; max_fuel; initial_ifuel; max_ifuel; detail_errors;
        detail_hint_replay; no_smt; quake_lo; quake_hi; quake_keep; retry;
        smtencoding_elim_box; smtencoding_nl_arith_repr;
        smtencoding_l_arith_repr; smtencoding_valid_intro;
        smtencoding_valid_elim; tcnorm; no_plugins; no_tactics; z3cliopt;
        z3smtopt; z3refresh; z3rlimit; z3rlimit_factor; z3seed; z3version;
        trivial_pre_for_unannotated_effectful_fns; reuse_hint_for;_} ->
        smtencoding_elim_box
let (__proj__Mkvconfig__item__smtencoding_nl_arith_repr :
  vconfig -> Prims.string) =
  fun projectee ->
    match projectee with
    | { initial_fuel; max_fuel; initial_ifuel; max_ifuel; detail_errors;
        detail_hint_replay; no_smt; quake_lo; quake_hi; quake_keep; retry;
        smtencoding_elim_box; smtencoding_nl_arith_repr;
        smtencoding_l_arith_repr; smtencoding_valid_intro;
        smtencoding_valid_elim; tcnorm; no_plugins; no_tactics; z3cliopt;
        z3smtopt; z3refresh; z3rlimit; z3rlimit_factor; z3seed; z3version;
        trivial_pre_for_unannotated_effectful_fns; reuse_hint_for;_} ->
        smtencoding_nl_arith_repr
let (__proj__Mkvconfig__item__smtencoding_l_arith_repr :
  vconfig -> Prims.string) =
  fun projectee ->
    match projectee with
    | { initial_fuel; max_fuel; initial_ifuel; max_ifuel; detail_errors;
        detail_hint_replay; no_smt; quake_lo; quake_hi; quake_keep; retry;
        smtencoding_elim_box; smtencoding_nl_arith_repr;
        smtencoding_l_arith_repr; smtencoding_valid_intro;
        smtencoding_valid_elim; tcnorm; no_plugins; no_tactics; z3cliopt;
        z3smtopt; z3refresh; z3rlimit; z3rlimit_factor; z3seed; z3version;
        trivial_pre_for_unannotated_effectful_fns; reuse_hint_for;_} ->
        smtencoding_l_arith_repr
let (__proj__Mkvconfig__item__smtencoding_valid_intro :
  vconfig -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { initial_fuel; max_fuel; initial_ifuel; max_ifuel; detail_errors;
        detail_hint_replay; no_smt; quake_lo; quake_hi; quake_keep; retry;
        smtencoding_elim_box; smtencoding_nl_arith_repr;
        smtencoding_l_arith_repr; smtencoding_valid_intro;
        smtencoding_valid_elim; tcnorm; no_plugins; no_tactics; z3cliopt;
        z3smtopt; z3refresh; z3rlimit; z3rlimit_factor; z3seed; z3version;
        trivial_pre_for_unannotated_effectful_fns; reuse_hint_for;_} ->
        smtencoding_valid_intro
let (__proj__Mkvconfig__item__smtencoding_valid_elim : vconfig -> Prims.bool)
  =
  fun projectee ->
    match projectee with
    | { initial_fuel; max_fuel; initial_ifuel; max_ifuel; detail_errors;
        detail_hint_replay; no_smt; quake_lo; quake_hi; quake_keep; retry;
        smtencoding_elim_box; smtencoding_nl_arith_repr;
        smtencoding_l_arith_repr; smtencoding_valid_intro;
        smtencoding_valid_elim; tcnorm; no_plugins; no_tactics; z3cliopt;
        z3smtopt; z3refresh; z3rlimit; z3rlimit_factor; z3seed; z3version;
        trivial_pre_for_unannotated_effectful_fns; reuse_hint_for;_} ->
        smtencoding_valid_elim
let (__proj__Mkvconfig__item__tcnorm : vconfig -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { initial_fuel; max_fuel; initial_ifuel; max_ifuel; detail_errors;
        detail_hint_replay; no_smt; quake_lo; quake_hi; quake_keep; retry;
        smtencoding_elim_box; smtencoding_nl_arith_repr;
        smtencoding_l_arith_repr; smtencoding_valid_intro;
        smtencoding_valid_elim; tcnorm; no_plugins; no_tactics; z3cliopt;
        z3smtopt; z3refresh; z3rlimit; z3rlimit_factor; z3seed; z3version;
        trivial_pre_for_unannotated_effectful_fns; reuse_hint_for;_} ->
        tcnorm
let (__proj__Mkvconfig__item__no_plugins : vconfig -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { initial_fuel; max_fuel; initial_ifuel; max_ifuel; detail_errors;
        detail_hint_replay; no_smt; quake_lo; quake_hi; quake_keep; retry;
        smtencoding_elim_box; smtencoding_nl_arith_repr;
        smtencoding_l_arith_repr; smtencoding_valid_intro;
        smtencoding_valid_elim; tcnorm; no_plugins; no_tactics; z3cliopt;
        z3smtopt; z3refresh; z3rlimit; z3rlimit_factor; z3seed; z3version;
        trivial_pre_for_unannotated_effectful_fns; reuse_hint_for;_} ->
        no_plugins
let (__proj__Mkvconfig__item__no_tactics : vconfig -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { initial_fuel; max_fuel; initial_ifuel; max_ifuel; detail_errors;
        detail_hint_replay; no_smt; quake_lo; quake_hi; quake_keep; retry;
        smtencoding_elim_box; smtencoding_nl_arith_repr;
        smtencoding_l_arith_repr; smtencoding_valid_intro;
        smtencoding_valid_elim; tcnorm; no_plugins; no_tactics; z3cliopt;
        z3smtopt; z3refresh; z3rlimit; z3rlimit_factor; z3seed; z3version;
        trivial_pre_for_unannotated_effectful_fns; reuse_hint_for;_} ->
        no_tactics
let (__proj__Mkvconfig__item__z3cliopt : vconfig -> Prims.string Prims.list)
  =
  fun projectee ->
    match projectee with
    | { initial_fuel; max_fuel; initial_ifuel; max_ifuel; detail_errors;
        detail_hint_replay; no_smt; quake_lo; quake_hi; quake_keep; retry;
        smtencoding_elim_box; smtencoding_nl_arith_repr;
        smtencoding_l_arith_repr; smtencoding_valid_intro;
        smtencoding_valid_elim; tcnorm; no_plugins; no_tactics; z3cliopt;
        z3smtopt; z3refresh; z3rlimit; z3rlimit_factor; z3seed; z3version;
        trivial_pre_for_unannotated_effectful_fns; reuse_hint_for;_} ->
        z3cliopt
let (__proj__Mkvconfig__item__z3smtopt : vconfig -> Prims.string Prims.list)
  =
  fun projectee ->
    match projectee with
    | { initial_fuel; max_fuel; initial_ifuel; max_ifuel; detail_errors;
        detail_hint_replay; no_smt; quake_lo; quake_hi; quake_keep; retry;
        smtencoding_elim_box; smtencoding_nl_arith_repr;
        smtencoding_l_arith_repr; smtencoding_valid_intro;
        smtencoding_valid_elim; tcnorm; no_plugins; no_tactics; z3cliopt;
        z3smtopt; z3refresh; z3rlimit; z3rlimit_factor; z3seed; z3version;
        trivial_pre_for_unannotated_effectful_fns; reuse_hint_for;_} ->
        z3smtopt
let (__proj__Mkvconfig__item__z3refresh : vconfig -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { initial_fuel; max_fuel; initial_ifuel; max_ifuel; detail_errors;
        detail_hint_replay; no_smt; quake_lo; quake_hi; quake_keep; retry;
        smtencoding_elim_box; smtencoding_nl_arith_repr;
        smtencoding_l_arith_repr; smtencoding_valid_intro;
        smtencoding_valid_elim; tcnorm; no_plugins; no_tactics; z3cliopt;
        z3smtopt; z3refresh; z3rlimit; z3rlimit_factor; z3seed; z3version;
        trivial_pre_for_unannotated_effectful_fns; reuse_hint_for;_} ->
        z3refresh
let (__proj__Mkvconfig__item__z3rlimit : vconfig -> Prims.int) =
  fun projectee ->
    match projectee with
    | { initial_fuel; max_fuel; initial_ifuel; max_ifuel; detail_errors;
        detail_hint_replay; no_smt; quake_lo; quake_hi; quake_keep; retry;
        smtencoding_elim_box; smtencoding_nl_arith_repr;
        smtencoding_l_arith_repr; smtencoding_valid_intro;
        smtencoding_valid_elim; tcnorm; no_plugins; no_tactics; z3cliopt;
        z3smtopt; z3refresh; z3rlimit; z3rlimit_factor; z3seed; z3version;
        trivial_pre_for_unannotated_effectful_fns; reuse_hint_for;_} ->
        z3rlimit
let (__proj__Mkvconfig__item__z3rlimit_factor : vconfig -> Prims.int) =
  fun projectee ->
    match projectee with
    | { initial_fuel; max_fuel; initial_ifuel; max_ifuel; detail_errors;
        detail_hint_replay; no_smt; quake_lo; quake_hi; quake_keep; retry;
        smtencoding_elim_box; smtencoding_nl_arith_repr;
        smtencoding_l_arith_repr; smtencoding_valid_intro;
        smtencoding_valid_elim; tcnorm; no_plugins; no_tactics; z3cliopt;
        z3smtopt; z3refresh; z3rlimit; z3rlimit_factor; z3seed; z3version;
        trivial_pre_for_unannotated_effectful_fns; reuse_hint_for;_} ->
        z3rlimit_factor
let (__proj__Mkvconfig__item__z3seed : vconfig -> Prims.int) =
  fun projectee ->
    match projectee with
    | { initial_fuel; max_fuel; initial_ifuel; max_ifuel; detail_errors;
        detail_hint_replay; no_smt; quake_lo; quake_hi; quake_keep; retry;
        smtencoding_elim_box; smtencoding_nl_arith_repr;
        smtencoding_l_arith_repr; smtencoding_valid_intro;
        smtencoding_valid_elim; tcnorm; no_plugins; no_tactics; z3cliopt;
        z3smtopt; z3refresh; z3rlimit; z3rlimit_factor; z3seed; z3version;
        trivial_pre_for_unannotated_effectful_fns; reuse_hint_for;_} ->
        z3seed
let (__proj__Mkvconfig__item__z3version : vconfig -> Prims.string) =
  fun projectee ->
    match projectee with
    | { initial_fuel; max_fuel; initial_ifuel; max_ifuel; detail_errors;
        detail_hint_replay; no_smt; quake_lo; quake_hi; quake_keep; retry;
        smtencoding_elim_box; smtencoding_nl_arith_repr;
        smtencoding_l_arith_repr; smtencoding_valid_intro;
        smtencoding_valid_elim; tcnorm; no_plugins; no_tactics; z3cliopt;
        z3smtopt; z3refresh; z3rlimit; z3rlimit_factor; z3seed; z3version;
        trivial_pre_for_unannotated_effectful_fns; reuse_hint_for;_} ->
        z3version
let (__proj__Mkvconfig__item__trivial_pre_for_unannotated_effectful_fns :
  vconfig -> Prims.bool) =
  fun projectee ->
    match projectee with
    | { initial_fuel; max_fuel; initial_ifuel; max_ifuel; detail_errors;
        detail_hint_replay; no_smt; quake_lo; quake_hi; quake_keep; retry;
        smtencoding_elim_box; smtencoding_nl_arith_repr;
        smtencoding_l_arith_repr; smtencoding_valid_intro;
        smtencoding_valid_elim; tcnorm; no_plugins; no_tactics; z3cliopt;
        z3smtopt; z3refresh; z3rlimit; z3rlimit_factor; z3seed; z3version;
        trivial_pre_for_unannotated_effectful_fns; reuse_hint_for;_} ->
        trivial_pre_for_unannotated_effectful_fns
let (__proj__Mkvconfig__item__reuse_hint_for :
  vconfig -> Prims.string FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with
    | { initial_fuel; max_fuel; initial_ifuel; max_ifuel; detail_errors;
        detail_hint_replay; no_smt; quake_lo; quake_hi; quake_keep; retry;
        smtencoding_elim_box; smtencoding_nl_arith_repr;
        smtencoding_l_arith_repr; smtencoding_valid_intro;
        smtencoding_valid_elim; tcnorm; no_plugins; no_tactics; z3cliopt;
        z3smtopt; z3refresh; z3rlimit; z3rlimit_factor; z3seed; z3version;
        trivial_pre_for_unannotated_effectful_fns; reuse_hint_for;_} ->
        reuse_hint_for
module FStar.Tactics.SMT

open FStar.Tactics.Effect
open FStar.Stubs.Tactics.V2.Builtins
open FStar.Stubs.VConfig

(* Alias to just use the current vconfig *)
let smt_sync () : Tac unit = t_smt_sync (get_vconfig ())

(* smt_sync': as smt_sync, but using a particular fuel/ifuel *)
let smt_sync' (fuel ifuel : nat) : Tac unit =
    let vcfg = get_vconfig () in
    let vcfg' = { vcfg with initial_fuel = fuel; max_fuel = fuel
                          ; initial_ifuel = ifuel; max_ifuel = ifuel }
    in
    t_smt_sync vcfg'

(* Getting/setting solver configuration *)

let get_rlimit () :               Tac int  = (get_vconfig()).z3rlimit
let set_rlimit (v : int) :        Tac unit = set_vconfig { get_vconfig () with z3rlimit = v }

let get_initial_fuel  () :        Tac int  = (get_vconfig ()).initial_fuel
let get_initial_ifuel () :        Tac int  = (get_vconfig ()).initial_ifuel
let get_max_fuel  () :            Tac int  = (get_vconfig ()).max_fuel
let get_max_ifuel () :            Tac int  = (get_vconfig ()).max_ifuel

let set_initial_fuel  (v : int) : Tac unit = set_vconfig { get_vconfig () with initial_fuel  = v }
let set_initial_ifuel (v : int) : Tac unit = set_vconfig { get_vconfig () with initial_ifuel = v }
let set_max_fuel  (v : int) :     Tac unit = set_vconfig { get_vconfig () with max_fuel      = v }
let set_max_ifuel (v : int) :     Tac unit = set_vconfig { get_vconfig () with max_ifuel     = v }

(* Set both min and max *)
let set_fuel  (v : int) :         Tac unit = set_vconfig { get_vconfig () with initial_fuel  = v; max_fuel  = v }
let set_ifuel (v : int) :         Tac unit = set_vconfig { get_vconfig () with initial_ifuel = v; max_ifuel = v }

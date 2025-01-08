module FStar.Tactics.SMT

open FStar.Tactics.Effect

(* Alias to just use the current vconfig *)
[@@plugin]
val smt_sync () : Tac unit

(* smt_sync': as smt_sync, but using a particular fuel/ifuel *)
[@@plugin]
val smt_sync' (fuel ifuel : nat) : Tac unit

(* Getting/setting solver configuration *)

[@@plugin]
val get_rlimit () :               Tac int 
[@@plugin]
val set_rlimit (v : int) :        Tac unit

[@@plugin]
val get_initial_fuel  () :        Tac int 
[@@plugin]
val get_initial_ifuel () :        Tac int 
[@@plugin]
val get_max_fuel  () :            Tac int 
[@@plugin]
val get_max_ifuel () :            Tac int 

[@@plugin]
val set_initial_fuel  (v : int) : Tac unit
[@@plugin]
val set_initial_ifuel (v : int) : Tac unit
[@@plugin]
val set_max_fuel  (v : int) :     Tac unit
[@@plugin]
val set_max_ifuel (v : int) :     Tac unit

(* Set both min and max *)
[@@plugin]
val set_fuel  (v : int) :         Tac unit
[@@plugin]
val set_ifuel (v : int) :         Tac unit

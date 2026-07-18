open Fstarcompiler
open Prims
type 'a tac_wp_t0 = unit
type ('a, 'wp) tac_wp_monotonic = unit
type 'a tac_wp_t = unit
type ('a, 'wp) tac_repr = FStarC_Tactics_Types.ref_proofstate -> 'a
type ('a, 'x, 'post) tac_return_wp = 'post
let tac_return (x : 'a) : ('a, Obj.t) tac_repr= fun uu___ -> x
type ('a, 'b, 'wpuf, 'wpug, 'post) tac_bind_wp = 'wpuf
type ('a, 'wp, 'post) tac_wp_compact = unit
let tac_bind (t1 : ('a, 'wpuf) tac_repr) (t2 : 'a -> ('b, 'wpug) tac_repr) :
  ('b, unit) tac_repr= fun ps -> let x = t1 ps in t2 x ps
type ('a, 'wputhen, 'wpuelse, 'b, 'post) tac_if_then_else_wp = unit
type ('a, 'wputhen, 'wpuelse, 'f, 'g, 'b) tac_if_then_else =
  ('a, unit) tac_repr
let tac_subcomp (uu___ : ('a, 'wpuf) tac_repr) : ('a, 'wpug) tac_repr=
  (fun f -> Obj.magic f) uu___
type ('a, 'b, 'wpuf, 'f) tac_close = ('a, unit) tac_repr
let __proj__TAC__item__return = tac_return
let __proj__TAC__item__bind = tac_bind
type ('a, 'wp, 'uuuuu) lift_div_tac_wp = 'wp
let lift_div_tac (f : unit -> 'a) : ('a, 'wp) tac_repr= fun uu___ -> f ()
type ('uuuuu, 'p) with_tactic = 'p
let rewrite_with_tactic (uu___ : unit -> (unit, unit) tac_repr)
  (uu___1 : unit) (p : Obj.t) : Obj.t= p
let synth_by_tactic (uu___ : unit -> (unit, unit) tac_repr) : 'uuuuu=
  Prims.admit ()
let assume_safe (tau : unit -> ('a, unit) tac_repr) : ('a, unit) tac_repr=
  tau ()
type ('a, 'b) tac = 'a -> ('b, unit) tac_repr
type 'a tactic = (unit, 'a) tac

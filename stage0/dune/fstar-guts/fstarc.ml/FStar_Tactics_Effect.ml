open Prims
type 'a tac_wp_t0 = unit
type 'a tac_wp_t = unit
type ('a, 'wp) tac_repr = FStarC_Tactics_Types.ref_proofstate -> 'a

let tac_return (x : 'a) : ('a, Obj.t) tac_repr= fun uu___ -> x


let tac_bind (wp_f : unit) (wp_g : unit) (t1 : ('a, Obj.t) tac_repr)
  (t2 : 'a -> ('b, Obj.t) tac_repr) : ('b, Obj.t) tac_repr=
  fun ps -> let x = t1 ps in t2 x ps

type ('a, 'wputhen, 'wpuelse, 'f, 'g, 'b) tac_if_then_else =
  ('a, Obj.t) tac_repr
let tac_subcomp (wp_f : unit) (wp_g : unit) (f : ('a, Obj.t) tac_repr) :
  ('a, Obj.t) tac_repr= f
type ('a, 'b, 'wpuf, 'f) tac_close = ('a, Obj.t) tac_repr
let __proj__TAC__item__return = tac_return
let __proj__TAC__item__bind = tac_bind

let lift_div_tac (wp : unit) (f : unit -> 'a) : ('a, Obj.t) tac_repr=
  fun uu___ -> f ()
let rewrite_with_tactic (uu___ : unit -> (unit, Obj.t) tac_repr)
  (uu___1 : unit) (p : Obj.t) : Obj.t= p
let synth_by_tactic (uu___ : unit -> (unit, Obj.t) tac_repr) : 'uuuuu=
  Prims.admit ()
let assume_safe (tau : unit -> ('a, Obj.t) tac_repr) : ('a, Obj.t) tac_repr=
  tau ()
type ('a, 'b) tac = 'a -> ('b, Obj.t) tac_repr
type 'a tactic = (unit, 'a) tac

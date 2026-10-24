module Bug4791
#lang-pulse
open Pulse

(* #4791: maybe_hoist rebuilt a stateful application from the original term,
   so a nested stateful argument at depth d was elaborated, and run in the
   checked program, 2^(d-1) times. *)

fn incr (r:ref int) (x:int)
  requires r |-> 'v
  returns y:int
  ensures r |-> ('v + 1) ** pure (y == x + 1)
{ r := !r + 1; (x + 1) }

fn three (r:ref int)
  requires r |-> 'v
  returns y:int
  ensures r |-> ('v + 3) ** pure (y == 3)
{ incr r (incr r (incr r 0)) }

fn eight (r:ref int)
  requires r |-> 'v
  returns y:int
  ensures r |-> ('v + 8) ** pure (y == 8)
{ incr r (incr r (incr r (incr r (incr r (incr r (incr r (incr r 0))))))) }

(* Exponential before the fix: depth 10 took about 3 minutes, depth 12 more
   than 10. *)
fn get (r:ref int) (x:int)
  preserves r |-> 'v
  returns y:int
  ensures pure (y == x + 1)
{ let _ = !r; (x + 1) }

fn deep (r:ref int)
  preserves r |-> 'v
  returns y:int
  ensures pure (y == 12)
{ get r (get r (get r (get r (get r (get r (get r (get r (get r (get r (get r (get r 0))))))))))) }

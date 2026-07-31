module Bug4347
#lang-pulse
open Pulse

let predicate p_pred (v: int) = emp

fn good ()
  returns r : (ref int)
  ensures exists* (v: int). (pts_to r #1.0R v ** p_pred v)
{ admit () }

let id_wrap (r: ref int) (p: slprop) : slprop = p

fn bad ()
  returns r : (ref int)
  ensures exists* (v: int). id_wrap r (pts_to r #1.0R v ** p_pred (!r))
{ admit () }

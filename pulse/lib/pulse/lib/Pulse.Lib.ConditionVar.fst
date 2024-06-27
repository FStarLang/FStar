module Pulse.Lib.ConditionVar
open Pulse.Lib.Pervasives
open Pulse.Lib.ConditionVarWithCodes
module CV = Pulse.Lib.ConditionVarWithCodes
////////////////////////////////////////////////////////////////
//Using condition vars directly with storable vprops
////////////////////////////////////////////////////////////////

let code : CV.code = {
  t = small_vprop;
  emp = down2 emp;
  up = (fun x -> up2_is_small x; up2 x);
  laws = ()
}

let code_of (p:storable) : CV.codeable code p = {
  c = down2 p;
  laws = ()
}

let cvar_t = CV.cvar_t code

let inv_name (c:cvar_t) = CV.inv_name c

let send (cv:cvar_t) (p:vprop) : vprop = CV.send cv p

let recv (cv:cvar_t) (p:vprop) : vprop = CV.recv cv p

let create (p:storable)
: stt cvar_t emp (fun b -> send b p ** recv b p)
= CV.create p (code_of p)

let signal (cv:cvar_t) (#p:vprop)
: stt unit (send cv p ** p) (fun _ -> emp)
= CV.signal cv #p

let wait (cv:cvar_t) (#p:vprop)
: stt unit (recv cv p) (fun _ -> p)
= CV.wait cv #p

let split (cv:cvar_t) (#p #q:storable)
: stt_ghost unit (add_inv emp_inames (inv_name cv))
  (recv cv (p ** q)) (fun _ -> recv cv p ** recv cv q)
= CV.split cv #p #q (code_of p) (code_of q)

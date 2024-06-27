module PulseExample.ConditionVarUseCodes
open Pulse.Lib.Pervasives
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

////////////////////////////////////////////////////////////////
//A custom language of codes allowing sending permissions to 
//a cvar over another cvar
////////////////////////////////////////////////////////////////

noeq
type cc (c:CV.code) : Type u#2 =
| Small of c.t
| Star : cc c -> cc c -> cc c
| Send : CV.cvar_t c -> cc c
| Recv : CV.cvar_t c -> c.t -> cc c

let rec up_cc #c (t:cc c)
: boxable
= match t with
  | Small s -> c.up s
  | Star c1 c2 ->
    up_cc c1 ** up_cc c2
  | Send cv ->
    CV.send_core cv
  | Recv cv s ->
    CV.recv_core cv (c.up s)

let cc_code (#c:CV.code) : CV.code = {
  t = cc c;
  emp = Small c.emp;
  up = up_cc;
  laws = ()
}

let code_of_send_core #c (cv:CV.cvar_t c) : CV.codeable cc_code (CV.send_core cv) = {
  c = Send cv;
  laws = ()
}

let code_of_recv_core #c 
    (cv:CV.cvar_t c)
    (s:vprop)
    (code_of_s:CV.codeable c s) 
: CV.codeable cc_code (CV.recv_core cv s) = {
  c = Recv cv code_of_s.c;
  laws = ()
}

```pulse
fn wait_indirect #c1 #c2 (cv1:CV.cvar_t c1) (cv2:CV.cvar_t c2) (#p:vprop)
requires
  CV.cvinv cv1 p **
  CV.recv cv2 (CV.send_core cv1) **
  p
ensures
  emp
{
  CV.wait cv2;
  CV.recompose_send cv1 _;
  CV.signal cv1;
}
```

```pulse
fn wait_direct #c (cv:CV.cvar_t c) (#p:storable)
requires CV.recv cv p
ensures p
{
  CV.wait cv;
}
```

```pulse
fn test_two (p:storable)
requires p
ensures p
{
  let cv1 = CV.create p (code_of p);
  let cv2 = CV.create #cc_code (CV.send_core cv1) (code_of_send_core cv1);
  CV.decompose_send cv1 _;
  CV.signal cv2;
  par (fun _ -> wait_indirect cv1 cv2) (fun _ -> wait_direct cv1);
}
```
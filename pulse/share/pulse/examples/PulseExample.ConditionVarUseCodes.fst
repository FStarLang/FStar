module PulseExample.ConditionVarUseCodes
open Pulse.Lib.Pervasives
module CV = Pulse.Lib.ConditionVarWithCodes

let free_code : CV.code = {
  t = slprop1_repr;
  emp = down1 emp;
  up = (fun x -> up1_is_slprop1 x; up1 x);
  laws = ()
}

let free_code_of (p:slprop1) : CV.codeable free_code p = {
  c = down1 p;
  laws = ()
}



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
: slprop2
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
    (s:slprop)
    (code_of_s:CV.codeable c s) 
: CV.codeable cc_code (CV.recv_core cv s) = {
  c = Recv cv code_of_s.c;
  laws = ()
}

```pulse
fn wait_indirect #c1 #c2 (cv1:CV.cvar_t c1) (cv2:CV.cvar_t c2) (#p:slprop)
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
fn wait_direct #c (cv:CV.cvar_t c) (#p:slprop2)
requires CV.recv cv p
ensures p
{
  CV.wait cv;
}
```

```pulse
fn test_two (p:slprop1)
requires p
ensures p
{
  let cv1 = CV.create p (free_code_of p);
  let cv2 = CV.create #cc_code (CV.send_core cv1) (code_of_send_core cv1);
  CV.decompose_send cv1 _;
  CV.signal cv2;
  par (fun _ -> wait_indirect cv1 cv2) (fun _ -> wait_direct cv1);
}
```
